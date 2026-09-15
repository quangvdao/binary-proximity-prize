#!/usr/bin/env python3
"""Record a local diagnostic only after benchmark.sh runs Comparator successfully."""
from __future__ import annotations
import sys
from benchmark_contract import (
    PROFILE_PARAMETERS, arklib_revision, atomic_write_json, atomic_write_text,
    parse_centibits, parse_radius, parse_unsafe_index, split_track, submission_revision,
)

def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit('usage: write-benchmark-score.py TRACK CENTIBITS CLAIM')
    track, raw_score, claim = sys.argv[1:]
    try:
        rate, side = split_track(track)
        p = PROFILE_PARAMETERS[rate]
        centibits = parse_centibits(raw_score)
        ns = 'ProximityPrize.Benchmark' + ('.Quarter' if rate == 'quarter' else '')
        if side == 'lower':
            numerator, denominator = parse_radius(claim)
            radius = f'{numerator}/{denominator}'
            kind = 'certified-bit-lower-bound'
        else:
            numerator = parse_unsafe_index(claim, profile=rate)
            denominator = p['domainSize']
            radius = f'{numerator}/{denominator}'
            kind = 'combinatorial-bit-upper-bound'
            ns += '.Upper'
        metrics = dict(p) | {
            'track': 'binary-' + track, 'profile': rate,
            'centibits': centibits, 'metric': 'security-bits',
            'field': 'GF(2^192)', 'evaluationPointBaseField': 'GF(2^64)',
            'sourceAlphabet': 'GF(2^192)', 'domain': 'LeanVM polynomial-basis prefix',
            'code': 'interleaved-Reed-Solomon', 'interleaving': 64,
            'claimKind': kind, 'radiusExact': radius,
            'reductionTarget': '2^-128', 'errorExpression': 'a^repetitions',
            'theorem': ns + '.candidate',
            'verified': False, 'locallyKernelChecked': True,
            'independentVerified': False, 'launchEligible': False,
            'verificationAuthority': 'local-comparator-diagnostic',
            'arklibRev': arklib_revision(), 'submissionRev': submission_revision(),
            'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        }
        if side == 'upper': metrics['unsafeIndex'] = numerator
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
    atomic_write_json(f'.yukon/binary-{track}-score.json', {'score': centibits / 100, 'metrics': metrics})
    atomic_write_text(f'benchmark-results/binary-{track}-summary.md',
        f'# Binary {track} local diagnostic\n\n'
        f'- Bit score: **{centibits / 100:.2f}**\n'
        f'- Exact radius: `{radius}`\n'
        f'- Profile: `{rate}`, N={p["domainSize"]}, K={p["baseDimension"]}, 64 lanes.\n'
        '- Reduction-error threshold: `2^-128`.\n'
        '- Official leaderboard receipt: **none**. This sample has no registered verifier service.\n')

if __name__ == '__main__': main()
