#!/usr/bin/env python3
"""Emit exact retained inputs for strategy-00038's two-cell Lean gate.

The output is numerical certificate data, not a Lean proof.  Selection and
semantic-file hashes are fail-closed so the two fixed cells cannot drift.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import check_atlas as C

HERE = Path(__file__).resolve().parent
TARGET = HERE / 'target-manifest.json'
PILOT = HERE / 'pilot.json'
SEMANTIC_FILES = ('model.py', 'expressions.py', 'expression_names.json',
                  'check_atlas.py')


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_selected(path, schema, band_index, cell_index, scale, mu):
    raw = json.loads(path.read_text())
    if set(raw) != {'schema', 'bands'} or raw['schema'] != schema:
        raise ValueError(f'{path.name}: schema mismatch')
    expected = C.expected_bands(schema)
    if len(raw['bands']) != len(expected):
        raise ValueError(f'{path.name}: incomplete campaign')
    band = raw['bands'][band_index]
    if set(band) != {'delta', 'cells'}:
        raise ValueError(f'{path.name}: malformed selected band')
    expected_scale, expected_lo, expected_hi = expected[band_index]
    if ([C.parse_q(x, 'band endpoint') for x in band['delta']] !=
            [expected_lo, expected_hi]):
        raise ValueError(f'{path.name}: selected band endpoints changed')
    if not 0 < len(band['cells']) <= 64:
        raise ValueError(f'{path.name}: subdivision cap violated')
    cell_raw = band['cells'][cell_index]
    cell = C.parse_cell(cell_raw)
    if cell['scale'] != scale or cell['mu'] != list(mu):
        raise ValueError(f'{path.name}: selected cell changed')
    return raw['schema'], band['delta'], cell_raw, cell


def atom_arguments(cell, whole):
    _, _, inputs, _ = C.model_inputs(cell, whole)
    s, p, u, v, w = inputs
    z = p + s*p*p + s*s*u
    a = Q(5, 12)*p + s*(43*p*p + 1056)/144 + s*s*v
    b = -44 + Q(19, 24)*p*p + s*p*(295*p*p - 14256)/216 + s*s*w
    A = 1 + s*z
    R = 2 + s*a
    e = 6*a - 2*z + s*b
    Y = s*A
    W = s*R
    V = s*(R + s*e)
    d4 = 1 + s*Y
    d3 = 1 + W*V
    # Preserve the generated multiplication grouping: (z/d4)*s^2 and
    # (e/d3)*s^2, rather than using dependency-simplified coordinate gaps.
    q4 = (z/d4)*(s*s)
    q3 = (e/d3)*(s*s)
    return {'s': s, 'W': W, 'q4': q4, 'q3': q3}


def selected_record(label, schema, delta, raw_cell, cell):
    checked = C.check_cell(cell, include_centered=True)
    if checked['status'] != 'ENCLOSURES_PASS':
        raise ValueError(f'{label}: selected cell no longer passes')
    full_atoms = atom_arguments(cell, True)
    center_atoms = atom_arguments(cell, False)
    atoms = {}
    for name in ('s', 'W', 'q4', 'q3'):
        record = C.centered_record(full_atoms[name], center_atoms[name])
        bound = max(abs(full_atoms[name].v.lo), abs(full_atoms[name].v.hi))
        if bound > C.SCALE // 2:
            raise ValueError(f'{label}: {name} remainder domain failed')
        record['half_margin'] = str(Q(C.SCALE // 2 - bound, C.SCALE))
        atoms[name] = record
    return {
        'label': label,
        'schema': schema,
        'delta': delta,
        'cell': raw_cell,
        'checked': checked,
        'remainder_arguments': atoms,
    }


def emit(output):
    target = load_selected(
        TARGET, C.TARGET_SCHEMA, 0, 0, Q(1, 126334),
        (Q(251, 20), Q(17821, 1280)))
    pilot_seam = load_selected(
        PILOT, C.PILOT_SCHEMA, 0, 0, Q(1, 126334),
        (Q(251, 20), Q(17821, 1280)))
    remote = load_selected(
        PILOT, C.PILOT_SCHEMA, 1, 0, Q(1, 25),
        (Q(125, 8), Q(8125, 512)))
    if target[2] != pilot_seam[2]:
        raise ValueError('target and pilot seam cells diverged')
    records = [
        selected_record('target-band-0-cell-0', *target),
        selected_record('pilot-band-1-cell-0', *remote),
    ]
    result = {
        'status': 'CENTERED_GATE_DATA_NOT_PROOF',
        'strategy_id': 'strategy-00038',
        'bits': C.BITS,
        'remainder_terms': C.TERMS,
        'coordinate_order': ['theta', 'tau_displacement', 'u_displacement',
                             'v_displacement', 'w_displacement'],
        'cells': records,
        'manifest_sha256': {
            TARGET.name: sha256(TARGET),
            PILOT.name: sha256(PILOT),
        },
        'semantic_sha256': {
            name: sha256(HERE / name) for name in SEMANTIC_FILES
        },
        'interpretation': (
            'Exact outward-rounded data for Lean replay; status and values are '
            'not kernel-checked proofs.'),
    }
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({
        'status': result['status'],
        'cells': len(records),
        'outputs_per_cell': len(records[0]['checked']['raw_outputs']),
        'coordinates': C.NVAR,
    }))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    emit(args.output)


if __name__ == '__main__':
    main()
