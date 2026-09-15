#!/usr/bin/env python3
"""Reproduce the finite support-tree arithmetic; this does not prove tree existence."""
import json
from math import prod
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def bound(d, h):
    n = 2**d
    k = n // 4
    m = k // 2**h
    bank = prod(2**(d-1) - 2**i for i in range(2**h - 1)) // {2: 3, 3: 576}[h]
    f = ((k - 2*m)*bank**2 + 2*m*bank) // 4
    holes = 2**192 - n
    bad = max(bank - f//holes - 1, (holes*bank**2 + holes*bank + 2*f - 1)//(holes*bank + 2*f) - 1)
    assert bad > 2**64
    return n, k, m, bank, f, bad

def main():
    claims = json.loads((ROOT/'initial-bounds.json').read_text())
    assert claims['reductionTarget'] == '2^-128'
    assert claims['challengeFieldSize'] == '2^192'
    assert claims['minimumWinningCount'] == str(2**64+1)
    primary = {(c['rate'],c['domainLog']) for c in claims['constructionBounds'] if c['primaryProfile']}
    assert primary == {('half',22),('quarter',21)}
    assert sum(c['primaryProfile'] for c in claims['constructionBounds']) == 2
    for claim in claims['constructionBounds']:
        assert claim['rate'] in {'half','quarter'}
        assert type(claim['primaryProfile']) is bool
        n,k,m,bank,f,bad = bound(claim['domainLog'], claim['height'])
        threshold = k+m+(k if claim['rate']=='half' else 0)
        assert claim['agreementPoints'] == threshold
        assert claim['badCountLower'] == str(bad)
        assert claim['unsafeIndex'] == n-threshold
        # Ceiling of -100*t*log2(agreement), checked using integers only.
        t = claim['repetitions']
        assert t == (256 if claim['rate']=='half' else 128)
        bits = claim['centibitsUpper']
        assert threshold**(100*t) * 2**bits >= n**(100*t)
        assert threshold**(100*t) * 2**(bits-1) < n**(100*t)
        assert claim['formalizationStatus'] == 'arithmetic-only; construction theorem not yet formalized'
        print(f'{claim["id"]}: exact count and score pass; not a ProtocolClaimUpper')

if __name__=='__main__': main()
