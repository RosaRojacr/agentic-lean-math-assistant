from __future__ import annotations

import argparse
import json
from pathlib import Path

from build_release import verify_candidate


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify an Agentic Lean Math Assistant release candidate"
    )
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args()
    manifest = verify_candidate(args.candidate)
    print(
        json.dumps(
            {
                "status": "passed",
                "candidate": str(args.candidate.expanduser().resolve()),
                "version": manifest["release"]["version"],
                "artifacts": len(manifest["artifacts"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
