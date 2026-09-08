from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"{path} must contain an object")
    return value


def normalized(value: str) -> str:
    return " ".join(value.casefold().split())


def extract_pdf_page(pdf: Path, page: int) -> str:
    completed = subprocess.run(
        ["pdftotext", "-f", str(page), "-l", str(page), str(pdf), "-"],
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    return normalized(completed.stdout)


def check_pdf(pdf: Path, *, min_pages: int, exact_pages: int | None = None) -> int:
    if not pdf.is_file() or pdf.stat().st_size < 10_000:
        raise ValueError(f"{pdf.name} is missing or too small")
    if pdf.read_bytes()[:5] != b"%PDF-":
        raise ValueError(f"{pdf.name} has no PDF signature")
    completed = subprocess.run(
        ["pdfinfo", str(pdf)],
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    match = re.search(r"^Pages:\s+(\d+)\s*$", completed.stdout, re.MULTILINE)
    if match is None:
        raise ValueError("pdfinfo did not report a page count")
    pages = int(match.group(1))
    if pages < min_pages:
        raise ValueError(f"{pdf.name} is unexpectedly short: {pages} pages")
    if exact_pages is not None and pages != exact_pages:
        raise ValueError(f"{pdf.name} must have {exact_pages} page(s), found {pages}")
    links = subprocess.run(
        ["pdfinfo", "-url", str(pdf)],
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    if "file://" in links.stdout:
        raise ValueError(f"{pdf.name} contains nonportable local file links")
    return pages


def main(output: Path) -> int:
    manifest = load_json(output / "report-claims.json")
    citations = load_json(output / "citations.json")
    proof_manifest = load_json(output / "proof-manifest.json")
    html_path = output / "Proof.html"
    pdf_path = output / "Proof.pdf"
    portfolio_html_path = output / "Portfolio.html"
    portfolio_pdf_path = output / "Portfolio.pdf"
    html = html_path.read_text(encoding="utf-8")
    portfolio_html = portfolio_html_path.read_text(encoding="utf-8")

    expected_claims = [
        claim
        for section in manifest.get("sections", [])
        for claim in section.get("claims", [])
    ]
    expected_ids = [str(claim["id"]) for claim in expected_claims]
    if len(expected_ids) != len(set(expected_ids)):
        raise ValueError("report manifest contains duplicate claim ids")
    if citations.get("claim_count") != len(expected_ids):
        raise ValueError("citation count does not match report manifest")
    coverage = citations.get("coverage")
    if coverage != {"cited": len(expected_ids), "uncited": 0}:
        raise ValueError(f"citation coverage is incomplete: {coverage}")
    citation_claims = citations.get("claims")
    if not isinstance(citation_claims, dict) or set(citation_claims) != set(expected_ids):
        raise ValueError("citations.json does not cover exactly the report claims")

    rendered_ids = re.findall(r'data-claim-id="([a-z0-9-]+)"', html)
    if rendered_ids != expected_ids:
        raise ValueError("rendered claim order or coverage differs from the manifest")
    if re.search(r'href="https?://', html):
        raise ValueError("Proof.html contains an external web dependency")

    source_pdf = output / "sources" / "Canete2010.pdf"
    page_cache: dict[int, str] = {}
    lean_citations = 0
    cmv_citations = 0
    for claim_id in expected_ids:
        claim_citations = citation_claims[claim_id]
        if not isinstance(claim_citations, list) or not claim_citations:
            raise ValueError(f"claim {claim_id} has no resolved citation")
        for citation in claim_citations:
            kind = citation.get("kind")
            if kind == "lean":
                lean_citations += 1
                source = output / "sources" / "lean" / str(citation["source"])
                source_page = source.with_name(source.name + ".html")
                if not source.is_file() or not source_page.is_file():
                    raise ValueError(f"claim {claim_id} has a missing Lean source page")
                if sha256(source) != citation.get("source_sha256"):
                    raise ValueError(f"claim {claim_id} Lean source hash mismatch")
                line = citation.get("line")
                if not isinstance(line, int) or line < 1:
                    raise ValueError(f"claim {claim_id} has an invalid Lean line")
                lines = source.read_text(encoding="utf-8").splitlines()
                local_name = str(citation["declaration"]).rsplit(".", 1)[-1]
                if line > len(lines) or local_name not in lines[line - 1]:
                    raise ValueError(
                        f"claim {claim_id} declaration is absent at its cited Lean line"
                    )
                if f'id="L{line}"' not in source_page.read_text(encoding="utf-8"):
                    raise ValueError(f"claim {claim_id} Lean anchor is absent")
            elif kind == "cmv":
                cmv_citations += 1
                if not source_pdf.is_file() or sha256(source_pdf) != citation.get(
                    "source_sha256"
                ):
                    raise ValueError(f"claim {claim_id} CMV PDF hash mismatch")
                page = citation.get("page")
                anchors = citation.get("anchors")
                if not isinstance(page, int) or not isinstance(anchors, list) or not anchors:
                    raise ValueError(f"claim {claim_id} has an incomplete CMV citation")
                text = page_cache.setdefault(page, extract_pdf_page(source_pdf, page))
                missing = [anchor for anchor in anchors if normalized(str(anchor)) not in text]
                if missing:
                    raise ValueError(
                        f"claim {claim_id} CMV page {page} misses anchors: {missing}"
                    )
            else:
                raise ValueError(f"claim {claim_id} has unknown citation kind {kind!r}")

    for document_name, document in (
        ("Proof.html", html),
        ("Portfolio.html", portfolio_html),
    ):
        hrefs = re.findall(r'href="([^"#]+)(?:#[^"]*)?"', document)
        missing_links = sorted(
            href
            for href in hrefs
            if not (output / href).is_file() and not href.startswith("#")
        )
        if missing_links:
            raise ValueError(f"{document_name} contains missing links: {missing_links}")

    required_portfolio_text = (
        "Rosa Pavlak",
        "Lean 4",
        "1 &lt; λ &lt; 1.2581840884",
        "Exact scope",
        "does not prove existence",
    )
    missing_portfolio_text = [
        text for text in required_portfolio_text if text not in portfolio_html
    ]
    if missing_portfolio_text:
        raise ValueError(
            f"Portfolio.html is missing required content: {missing_portfolio_text}"
        )

    if proof_manifest.get("root") != "RangeReduction.lean":
        raise ValueError("proof manifest does not identify RangeReduction.lean")
    declarations = set(proof_manifest.get("declarations", []))
    if declarations != {
        "cmv_range_reduction",
        "cmv_type_four_range_reduction",
        "cmv_type_three_branch_contract",
    }:
        raise ValueError("proof manifest has an unexpected declaration surface")

    pages = check_pdf(pdf_path, min_pages=5)
    portfolio_pages = check_pdf(portfolio_pdf_path, min_pages=1, exact_pages=1)
    result = {
        "schema_version": 1,
        "status": "passed",
        "claim_count": len(expected_ids),
        "lean_citations": lean_citations,
        "cmv_citations": cmv_citations,
        "cmv_pages_checked": sorted(page_cache),
        "pdf_pages": pages,
        "portfolio_pdf_pages": portfolio_pages,
        "artifacts": {
            "Proof.html": sha256(html_path),
            "Proof.pdf": sha256(pdf_path),
            "Portfolio.html": sha256(portfolio_html_path),
            "Portfolio.pdf": sha256(portfolio_pdf_path),
            "citations.json": sha256(output / "citations.json"),
            "proof-manifest.json": sha256(output / "proof-manifest.json"),
        },
    }
    (output / "verification" / "report-verification.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        f"REPORT_CHECK_PASS claims={len(expected_ids)} "
        f"lean_citations={lean_citations} cmv_citations={cmv_citations} "
        f"pdf_pages={pages} portfolio_pages={portfolio_pages}"
    )
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--bundle", type=Path, default=Path("deliverable"))
    raise SystemExit(main(parser.parse_args().bundle.expanduser().resolve()))
