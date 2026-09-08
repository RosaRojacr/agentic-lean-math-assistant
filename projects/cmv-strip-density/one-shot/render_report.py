from __future__ import annotations

import hashlib
import html
import json
import os
import re
import shutil
import subprocess
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
CLAIMS_PATH = ROOT / "report" / "report-claims.json"
PROOF = ROOT / "proof"
OUTPUT = ROOT / "deliverable"
LEAN_OUTPUT = OUTPUT / "sources" / "lean"
DECLARATION = re.compile(
    r"\b(?:def|theorem|lemma|abbrev|structure|class)\s+({name})(?:\s|\{{|\(|:|$)"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"{path} must contain a JSON object")
    return value


def declaration_line(path: Path, declaration: str) -> int:
    local_name = declaration.rsplit(".", 1)[-1]
    pattern = re.compile(DECLARATION.pattern.format(name=re.escape(local_name)))
    matches = [
        index
        for index, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1)
        if pattern.search(line)
    ]
    if len(matches) != 1:
        raise ValueError(
            f"expected one source declaration {declaration!r} in {path}, found {matches}"
        )
    return matches[0]


def validate_manifest(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    if manifest.get("schema_version") != 1:
        raise ValueError("report manifest schema_version must be 1")
    skills = manifest.get("skills")
    if (
        not isinstance(skills, list)
        or not skills
        or not all(isinstance(skill, str) and skill.strip() for skill in skills)
    ):
        raise TypeError("report manifest skills must be a nonempty string array")
    sections = manifest.get("sections")
    if not isinstance(sections, list) or not sections:
        raise ValueError("report manifest must contain nonempty sections")
    claims: list[dict[str, Any]] = []
    seen: set[str] = set()
    for section in sections:
        if not isinstance(section, dict) or not isinstance(section.get("claims"), list):
            raise TypeError("each report section must contain a claims array")
        for claim in section["claims"]:
            if not isinstance(claim, dict):
                raise TypeError("each report claim must be an object")
            claim_id = claim.get("id")
            if not isinstance(claim_id, str) or not claim_id:
                raise ValueError("each report claim needs a nonempty id")
            if claim_id in seen:
                raise ValueError(f"duplicate report claim id: {claim_id}")
            seen.add(claim_id)
            if not isinstance(claim.get("statement"), str) or not claim["statement"]:
                raise ValueError(f"claim {claim_id} needs a statement")
            citations = claim.get("citations")
            if not isinstance(citations, list) or not citations:
                raise ValueError(f"claim {claim_id} has no citation")
            claims.append(claim)
    return claims


def render_lean_source(
    source: Path, destination: Path, referenced_lines: set[int]
) -> None:
    lines = source.read_text(encoding="utf-8").splitlines()
    rows: list[str] = []
    for number, line in enumerate(lines, 1):
        selected = " cited" if number in referenced_lines else ""
        rows.append(
            f'<div class="line{selected}" id="L{number}">'
            f'<a class="ln" href="#L{number}">{number}</a>'
            f'<code>{html.escape(line) or " "}</code></div>'
        )
    page = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{html.escape(source.name)} — cited Lean source</title>
<style>
:root{{--ink:#17212b;--muted:#667784;--paper:#fbfaf6;--line:#e5e0d5;--accent:#146c73}}
*{{box-sizing:border-box}} body{{margin:0;background:var(--paper);color:var(--ink);font:14px/1.45 ui-monospace,SFMono-Regular,Consolas,monospace}}
header{{position:sticky;top:0;padding:1rem 1.5rem;background:#12343b;color:white;z-index:2}} header small{{display:block;color:#cde3e2;margin-top:.25rem}}
.source{{padding:1rem 0 4rem}} .line{{display:grid;grid-template-columns:5rem 1fr;min-height:1.45rem;border-left:4px solid transparent}}
.line:target,.line.cited{{background:#fff4c7;border-left-color:#d99118}} .ln{{padding:0 1rem;color:var(--muted);text-align:right;text-decoration:none;user-select:none}}
code{{white-space:pre;overflow-wrap:normal}}
</style></head><body><header>{html.escape(source.name)}<small>SHA-256 {sha256(source)}</small></header><main class="source">{''.join(rows)}</main></body></html>
"""
    destination.write_text(page, encoding="utf-8")


def resolve_citations(
    manifest: dict[str, Any], claims: list[dict[str, Any]]
) -> tuple[dict[str, list[dict[str, Any]]], dict[str, set[int]]]:
    cmv = manifest.get("cmv_source")
    if not isinstance(cmv, dict):
        raise TypeError("cmv_source must be an object")
    cmv_path = ROOT / str(cmv.get("path", ""))
    if not cmv_path.is_file():
        raise ValueError(f"retained CMV PDF is missing: {cmv_path}")
    actual_cmv_hash = sha256(cmv_path)
    if actual_cmv_hash != cmv.get("sha256"):
        raise ValueError("retained CMV PDF hash does not match the report manifest")

    resolved: dict[str, list[dict[str, Any]]] = {}
    lean_lines: dict[str, set[int]] = {}
    for claim in claims:
        claim_id = str(claim["id"])
        resolved_claim: list[dict[str, Any]] = []
        for citation in claim["citations"]:
            if not isinstance(citation, dict):
                raise TypeError(f"claim {claim_id} has a malformed citation")
            kind = citation.get("kind")
            if kind == "cmv":
                locator = citation.get("locator")
                page = citation.get("page")
                anchors = citation.get("anchors")
                if (
                    not isinstance(locator, str)
                    or not locator
                    or not isinstance(page, int)
                    or not isinstance(anchors, list)
                    or not anchors
                    or not all(isinstance(anchor, str) and anchor for anchor in anchors)
                ):
                    raise ValueError(f"claim {claim_id} has an incomplete CMV citation")
                resolved_claim.append(
                    {
                        "kind": "cmv",
                        "source": "Canete2010.pdf",
                        "source_sha256": actual_cmv_hash,
                        "locator": locator,
                        "page": page,
                        "anchors": anchors,
                        "href": f"sources/Canete2010.pdf#page={page}",
                    }
                )
            elif kind == "lean":
                file_name = citation.get("file")
                declaration = citation.get("declaration")
                if not isinstance(file_name, str) or not isinstance(declaration, str):
                    raise ValueError(f"claim {claim_id} has an incomplete Lean citation")
                source = PROOF / file_name
                if not source.is_file() or source.suffix != ".lean":
                    raise ValueError(f"claim {claim_id} cites missing Lean file {file_name}")
                line = declaration_line(source, declaration)
                lean_lines.setdefault(file_name, set()).add(line)
                resolved_claim.append(
                    {
                        "kind": "lean",
                        "source": file_name,
                        "source_sha256": sha256(source),
                        "declaration": declaration,
                        "line": line,
                        "href": f"sources/lean/{file_name}.html#L{line}",
                    }
                )
            else:
                raise ValueError(f"claim {claim_id} has unknown citation kind {kind!r}")
        resolved[claim_id] = resolved_claim
    return resolved, lean_lines


def citation_html(citation: dict[str, Any]) -> str:
    href = html.escape(str(citation["href"]), quote=True)
    if citation["kind"] == "cmv":
        label = f"CMV: {citation['locator']}, p. {citation['page']}"
    else:
        label = (
            f"Lean: {citation['source']}:{citation['line']} · "
            f"{citation['declaration']}"
        )
    return f'<a class="citation" href="{href}">{html.escape(label)}</a>'


def claim_html(claim: dict[str, Any], citations: list[dict[str, Any]]) -> str:
    display = ""
    if isinstance(claim.get("display"), str):
        display = f'<div class="formula">{html.escape(claim["display"])}</div>'
    details = "".join(
        f"<p>{html.escape(str(detail))}</p>" for detail in claim.get("details", [])
    )
    cite = "".join(citation_html(item) for item in citations)
    return f"""<article class="claim" data-claim-id="{html.escape(str(claim['id']), quote=True)}">
<div class="claim-mark">VERIFIED CLAIM</div>
<h3>{html.escape(str(claim['title']))}</h3>
<p>{html.escape(str(claim['statement']))}</p>{display}{details}
<footer>{cite}</footer></article>"""

def build_portfolio_html(
    manifest: dict[str, Any],
    claims: list[dict[str, Any]],
    resolved: dict[str, list[dict[str, Any]]],
) -> str:
    modeled = next(claim for claim in claims if claim["id"] == "modeled-range")
    citations = "".join(citation_html(item) for item in resolved["modeled-range"])
    skills = " · ".join(html.escape(str(skill)) for skill in manifest["skills"])
    contract = ROOT / "contracts" / "report-contract.lean"
    audited = contract.read_text(encoding="utf-8").count("#print axioms")
    manifest_hash = sha256(CLAIMS_PATH)
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{html.escape(str(manifest['title']))} — Portfolio Summary</title>
<style>
@page {{ size:A4; margin:0 }}
:root{{--ink:#17242c;--teal:#0e5e65;--deep:#123b43;--paper:#f7f5ee;--gold:#d39b2e;--rule:#d8d5ca}}
*{{box-sizing:border-box}} body{{margin:0;background:#dfe6e2;color:var(--ink);font:15px/1.48 ui-sans-serif,system-ui,sans-serif}}
.sheet{{width:210mm;min-height:297mm;margin:0 auto;background:var(--paper);padding:17mm 18mm 14mm;display:flex;flex-direction:column;gap:6mm}}
header{{border-bottom:3px solid var(--deep);padding-bottom:5mm}} .eyebrow{{font-weight:800;letter-spacing:.16em;text-transform:uppercase;color:var(--teal);font-size:9px}}
h1{{font:700 32px/1.02 Georgia,serif;color:var(--deep);margin:2mm 0}} .subtitle{{font-size:15px;color:#4c6269}} .byline{{margin-top:3mm;font-weight:700}}
.skills{{color:var(--teal);font:700 10px/1.3 ui-monospace,monospace;margin-top:1.5mm}}
.result{{background:var(--deep);color:white;padding:6mm;border-left:4px solid var(--gold)}} .result b{{display:block;font:700 19px/1.2 Georgia,serif;margin-bottom:2mm}} .formula{{font:700 18px/1.2 Georgia,serif;margin:3mm 0}}
.metrics{{display:grid;grid-template-columns:repeat(3,1fr);gap:4mm}} .metric{{background:#e9eee8;padding:4mm;font-size:10px}} .metric strong{{display:block;font-size:22px;color:var(--deep)}}
.grid{{display:grid;grid-template-columns:1fr 1fr;gap:6mm}} h2{{font:700 16px/1.2 Georgia,serif;color:var(--deep);margin:0 0 2mm;border-top:2px solid var(--teal);padding-top:2mm}}
p{{margin:0 0 2.5mm}} ul{{margin:0;padding-left:5mm}} li{{margin:0 0 1.5mm}} .boundary{{background:#fff;border:1px solid var(--rule);padding:4mm}}
.citations{{display:flex;gap:2mm;flex-wrap:wrap;margin-top:3mm}} .citation{{border:1px solid #b8c9c5;border-radius:99px;padding:1.5mm 2.5mm;color:var(--deep);font-size:8px;text-decoration:none}} .result .citation{{color:#dcefed;border-color:#79a9a5}}
footer{{margin-top:auto;border-top:1px solid var(--rule);padding-top:3mm;display:flex;justify-content:space-between;gap:4mm;font:9px/1.35 ui-monospace,monospace;color:#516269}} footer a{{color:var(--teal)}}
@media(max-width:800px){{.sheet{{width:auto;min-height:100vh;padding:1.5rem}}.grid{{grid-template-columns:1fr}}}}
@media print{{body{{background:white}}.sheet{{margin:0}}a{{color:inherit;text-decoration:none}}}}
</style></head><body><main class="sheet">
<header><div class="eyebrow">Applied mathematics · formal methods · scientific computing</div>
<h1>{html.escape(str(manifest['title']))}</h1><div class="subtitle">{html.escape(str(manifest['subtitle']))}</div>
<div class="byline">{html.escape(str(manifest['authors']))}</div><div class="skills">{skills}</div></header>
<section class="result"><b>Machine-checked modeled result</b><div class="formula">1 &lt; λ &lt; 1.2581840884</div>
{html.escape(str(modeled['statement']))}<div class="citations">{citations}</div></section>
<div class="metrics"><div class="metric"><strong>{audited}</strong>Lean declarations axiom-audited</div>
<div class="metric"><strong>{len(claims)}/{len(claims)}</strong>technical claims cited</div>
<div class="metric"><strong>3</strong>independent proof, certificate, and document gates</div></div>
<div class="grid"><section><h2>What I built</h2><ul>
<li>A Lean 4 proof contract with explicit declaration and axiom checks.</li>
<li>An exact rational/Taylor certificate replay for the decimal cutoff.</li>
<li>A fail-closed citation resolver linking claims to paper pages and Lean source lines.</li>
<li>A one-command campaign retaining hashes, receipts, sources, HTML, and PDF.</li>
</ul></section><section><h2>Why it matters</h2><p>The project connects analytic reasoning, executable mathematics, and software assurance. A failed proof, certificate, citation, render, or independent review cannot be promoted as a successful result.</p>
<p>The full report exposes every verification boundary instead of treating generated prose as proof.</p></section></div>
<section class="boundary"><h2>Exact scope</h2><p>The formal theorem concerns an explicitly modeled <code>FourArcCandidate</code>. It does not prove existence of a type-(iv) minimizer or the full CMV conjecture. Applying it to arbitrary source-level minimizers still requires the published reduction and a source-to-coordinate correspondence.</p></section>
<footer><span>Full technical report: <a href="Proof.html">Proof.html</a> · Evidence: <a href="citations.json">citations.json</a></span><span>manifest {manifest_hash[:16]}</span></footer>
</main></body></html>"""


def build_html(
    manifest: dict[str, Any], resolved: dict[str, list[dict[str, Any]]]
) -> str:
    sections_html: list[str] = []
    nav: list[str] = []
    total = 0
    for index, section in enumerate(manifest["sections"], 1):
        section_id = str(section["id"])
        nav.append(
            f'<a href="#{html.escape(section_id, quote=True)}">'
            f'{index:02d} {html.escape(str(section["title"]))}</a>'
        )
        cards = []
        for claim in section["claims"]:
            total += 1
            cards.append(claim_html(claim, resolved[str(claim["id"])]))
        sections_html.append(
            f'<section id="{html.escape(section_id, quote=True)}">'
            f'<div class="section-number">{index:02d}</div>'
            f'<h2>{html.escape(str(section["title"]))}</h2>{"".join(cards)}</section>'
        )
    bibliography = html.escape(str(manifest["cmv_source"]["bibliography"]))
    skills = " · ".join(html.escape(str(skill)) for skill in manifest["skills"])
    manifest_hash = sha256(CLAIMS_PATH)
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{html.escape(str(manifest['title']))}</title>
<style>
@page {{ size: A4; margin: 18mm 17mm 20mm; @bottom-center {{ content: counter(page); font: 9pt sans-serif; color: #687783; }} }}
:root{{--ink:#16232c;--muted:#61717d;--paper:#f7f5ee;--card:#fffefa;--teal:#0f6067;--teal-dark:#123b43;--gold:#c98a16;--rule:#dcd7ca;--green:#27745f}}
*{{box-sizing:border-box}} html{{scroll-behavior:smooth}} body{{margin:0;background:var(--paper);color:var(--ink);font:17px/1.62 Georgia,'Times New Roman',serif}}
a{{color:var(--teal)}} .cover{{min-height:94vh;padding:9vh max(7vw,2rem) 5vh;background:linear-gradient(145deg,#0b3038,#175b61 66%,#d2a342);color:white;display:flex;flex-direction:column;justify-content:space-between}}
.eyebrow{{font:700 .78rem/1.2 ui-sans-serif,sans-serif;letter-spacing:.18em;text-transform:uppercase;color:#cbe7e3}} h1{{font:700 clamp(3rem,8vw,6.5rem)/.93 Georgia,serif;max-width:10ch;margin:.35em 0 .15em}} .subtitle{{font:1.35rem/1.4 ui-sans-serif,sans-serif;max-width:48rem;color:#e8f2ef}}
.result-box{{margin-top:2rem;padding:1.4rem 1.6rem;border-left:5px solid #f3c45d;background:#ffffff16;max-width:48rem}} .result-box strong{{display:block;font:700 1.45rem/1.3 ui-sans-serif,sans-serif}} .cover-meta{{display:flex;gap:2rem;flex-wrap:wrap;font:.85rem/1.4 ui-monospace,monospace;color:#d5e4e2}}
.layout{{display:grid;grid-template-columns:17rem minmax(0,52rem);gap:4rem;max-width:78rem;margin:0 auto;padding:4rem 2rem 7rem}} nav{{position:sticky;top:2rem;align-self:start;border-top:3px solid var(--teal-dark);padding-top:1rem}} nav a{{display:block;padding:.55rem 0;border-bottom:1px solid var(--rule);font:600 .82rem/1.3 ui-sans-serif,sans-serif;text-decoration:none;color:var(--teal-dark)}}
section{{position:relative;margin:0 0 5rem}} .section-number{{font:700 .8rem ui-monospace,monospace;color:var(--gold);letter-spacing:.15em}} h2{{font:700 2.25rem/1.15 Georgia,serif;margin:.25rem 0 1.6rem;color:var(--teal-dark)}} .claim{{background:var(--card);border:1px solid var(--rule);border-top:4px solid var(--teal);padding:1.45rem 1.55rem 1.25rem;margin:0 0 1.35rem;break-inside:avoid;box-shadow:0 8px 22px #1c31350c}}
.claim-mark{{font:700 .66rem/1 ui-sans-serif,sans-serif;letter-spacing:.16em;color:var(--green);margin-bottom:.6rem}} h3{{font:700 1.28rem/1.25 ui-sans-serif,sans-serif;margin:.2rem 0 .65rem;color:var(--ink)}} p{{margin:.5rem 0}} .formula{{margin:1rem 0;padding:1rem 1.2rem;background:#edf5f2;border-left:4px solid var(--green);font:600 1.08rem/1.5 'Times New Roman',serif;text-align:center;letter-spacing:.01em}}
.claim footer{{display:flex;flex-wrap:wrap;gap:.45rem;margin-top:1rem;padding-top:.85rem;border-top:1px solid var(--rule)}} .citation{{display:inline-block;border-radius:999px;background:#e6f0ef;padding:.38rem .7rem;font:600 .72rem/1.2 ui-sans-serif,sans-serif;text-decoration:none;color:var(--teal-dark)}} .citation:hover{{background:#d2e6e3}}
.references{{border-top:3px solid var(--teal-dark);padding-top:1.2rem}} .references h2{{font-size:1.7rem}} .coverage{{display:grid;grid-template-columns:repeat(3,1fr);gap:1rem;margin:1.5rem 0}} .metric{{padding:1rem;background:#eef2eb;font:700 .82rem/1.3 ui-sans-serif,sans-serif}} .metric b{{display:block;font-size:1.7rem;color:var(--teal-dark)}} code{{font-family:ui-monospace,monospace}}
@media(max-width:850px){{.layout{{display:block;padding:2rem 1rem}} nav{{position:static;margin-bottom:3rem}} .cover{{min-height:80vh}}}}
@media print{{body{{background:white;font-size:11pt}} .cover{{min-height:245mm;break-after:page;padding:25mm 18mm}} .layout{{display:block;max-width:none;padding:0}} nav{{display:none}} section{{break-before:page;margin:0}} section:first-of-type{{break-before:auto}} .claim{{box-shadow:none}} a{{color:inherit;text-decoration:none}} .citation{{border:1px solid #bfcac5;background:white}}}}
</style></head><body>
<header class="cover"><div><div class="eyebrow">Formal mathematics · cited evidence edition</div><h1>{html.escape(str(manifest['title']))}</h1><div class="subtitle">{html.escape(str(manifest['subtitle']))}</div><div class="result-box"><strong>Certified modeled conclusion</strong>Every modeled type-(iv) minimizer lies in 1 &lt; λ &lt; 1.2581840884. The source-level transfer remains explicit and conditional.</div></div><div class="cover-meta"><span>{html.escape(str(manifest['authors']))}</span><span>{skills}</span><span>{total} cited claims</span><span>manifest {manifest_hash[:16]}</span></div></header>
<div class="layout"><nav>{''.join(nav)}<a href="#references">References and coverage</a></nav><main>{''.join(sections_html)}
<section class="references" id="references"><div class="section-number">SOURCE</div><h2>References and coverage</h2><p>{bibliography}</p><div class="coverage"><div class="metric"><b>{total}/{total}</b>claims cited</div><div class="metric"><b>2</b>source classes</div><div class="metric"><b>fail closed</b>missing citation policy</div></div><p>Machine-readable resolution: <a href="citations.json"><code>citations.json</code></a>. Exact proof inventory: <a href="proof-manifest.json"><code>proof-manifest.json</code></a>. The CMV PDF and every cited Lean source are bundled under <code>sources/</code>.</p></section></main></div></body></html>
"""


def render_pdf(html_path: Path, pdf_path: Path) -> None:
    browser = os.environ.get("CHROMIUM") or shutil.which("chromium-browser") or shutil.which("chromium")
    if browser is None:
        raise RuntimeError("Chromium is required to render the PDF")
    profile = OUTPUT / ".chromium-profile"
    profile.mkdir(parents=True, exist_ok=True)
    command = [
        browser,
        "--headless=new",
        "--disable-gpu",
        "--disable-dev-shm-usage",
        "--no-sandbox",
        "--no-pdf-header-footer",
        f"--user-data-dir={profile}",
        f"--print-to-pdf={pdf_path.resolve()}",
        html_path.resolve().as_uri(),
    ]
    completed = subprocess.run(
        command, capture_output=True, text=True, timeout=180, check=False
    )
    shutil.rmtree(profile, ignore_errors=True)
    if completed.returncode != 0:
        raise RuntimeError(f"Chromium PDF rendering failed: {completed.stderr.strip()}")
    if not pdf_path.is_file() or pdf_path.stat().st_size < 10_000:
        raise RuntimeError("Chromium did not produce a substantive PDF")

def render_document(stem: str, document: str) -> None:
    html_path = OUTPUT / f"{stem}.html"
    html_path.write_text(document, encoding="utf-8")
    print_path = OUTPUT / f".{stem}-print.html"
    print_path.write_text(re.sub(r' href="[^"]*"', "", document), encoding="utf-8")
    try:
        render_pdf(print_path, OUTPUT / f"{stem}.pdf")
    finally:
        print_path.unlink(missing_ok=True)


def main() -> int:
    manifest = load_json(CLAIMS_PATH)
    claims = validate_manifest(manifest)
    resolved, lean_lines = resolve_citations(manifest, claims)

    if OUTPUT.exists():
        shutil.rmtree(OUTPUT)
    LEAN_OUTPUT.mkdir(parents=True)
    shutil.copytree(
        PROOF,
        OUTPUT / "proof",
        ignore=shutil.ignore_patterns(".lake", "__pycache__", "*.pyc"),
    )

    cmv_path = ROOT / str(manifest["cmv_source"]["path"])
    shutil.copy2(cmv_path, OUTPUT / "sources" / "Canete2010.pdf")
    for file_name, lines in sorted(lean_lines.items()):
        source = PROOF / file_name
        shutil.copy2(source, LEAN_OUTPUT / file_name)
        render_lean_source(source, LEAN_OUTPUT / f"{file_name}.html", lines)

    proof_manifest = PROOF / "proof-manifest.json"
    if not proof_manifest.is_file():
        raise ValueError("proof assembler did not produce proof-manifest.json")
    shutil.copy2(proof_manifest, OUTPUT / "proof-manifest.json")
    shutil.copy2(CLAIMS_PATH, OUTPUT / "report-claims.json")
    verification = OUTPUT / "verification"
    verification.mkdir()
    contract = ROOT / "contracts" / "report-contract.lean"
    if not contract.is_file():
        raise ValueError("immutable report contract is missing")
    shutil.copy2(contract, verification / contract.name)
    report_verifier = ROOT / "tools" / "verify_report.py"
    if not report_verifier.is_file():
        raise ValueError("portable report verifier is missing")
    shutil.copy2(report_verifier, verification / "verify_bundle.py")
    for name in ("verify_certificate.py", "optimization.json"):
        source = PROOF / name
        if not source.is_file():
            raise ValueError(f"proof verification input is missing: {name}")
        shutil.copy2(source, verification / name)

    citation_record = {
        "schema_version": 1,
        "claim_manifest_sha256": sha256(CLAIMS_PATH),
        "claim_count": len(claims),
        "coverage": {"cited": len(resolved), "uncited": 0},
        "claims": resolved,
    }
    (OUTPUT / "citations.json").write_text(
        json.dumps(citation_record, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    render_document("Portfolio", build_portfolio_html(manifest, claims, resolved))
    render_document("Proof", build_html(manifest, resolved))
    print(f"rendered {len(claims)} cited claims")
    print("created Portfolio and Proof HTML/PDF deliverables")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
