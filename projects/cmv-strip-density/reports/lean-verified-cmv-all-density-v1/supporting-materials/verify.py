from __future__ import annotations
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

supporting = pathlib.Path(__file__).resolve().parent
package = supporting.parent
checksums = supporting / "CHECKSUMS.sha256"
errors = []
for raw in checksums.read_text(encoding="utf-8").splitlines():
    if not raw.strip():
        continue
    expected, relative = raw.split("  ", 1)
    path = package / relative
    if not path.is_file():
        errors.append(f"missing: {relative}")
        continue
    observed = hashlib.sha256(path.read_bytes()).hexdigest()
    if observed != expected:
        errors.append(f"digest mismatch: {relative}")
if errors:
    print("Package integrity failed:", *errors, sep="\n- ", file=sys.stderr)
    raise SystemExit(1)

inventory = json.loads(
    (supporting / "declaration-inventory.json").read_text(encoding="utf-8")
)
modules = set(inventory["module_closure"])
import_pattern = re.compile(r"^[ \t]*import[ \t]+(?P<modules>[^\n-]+)", re.MULTILINE)

with tempfile.TemporaryDirectory(
    prefix=".proof-package-verify-", dir=package.parent
) as temporary:
    lean = pathlib.Path(temporary) / "lean"
    shutil.copytree(supporting / "lean", lean)
    visiting = set()
    visited = set()
    order = []

    def visit(module):
        if module in visited:
            return
        if module in visiting:
            raise SystemExit(f"local Lean import cycle at {module}")
        visiting.add(module)
        source = lean / (module.replace(".", "/") + ".lean")
        text = source.read_text(encoding="utf-8")
        for match in import_pattern.finditer(text):
            for imported in match.group("modules").split():
                if imported in modules:
                    visit(imported)
        visiting.remove(module)
        visited.add(module)
        order.append(module)

    for module in sorted(modules):
        visit(module)
    setup = subprocess.run(["lake", "update"], cwd=lean, check=False)
    if setup.returncode:
        raise SystemExit(setup.returncode)
    for module in order:
        result = subprocess.run(
            ["lake", "--old", "build", f"+{module}:olean"], cwd=lean, check=False
        )
        if result.returncode:
            raise SystemExit(result.returncode)
print("Package digests and pinned Lean build verified.")
