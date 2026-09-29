#!/usr/bin/env python3
"""Exact local-law and rank-window checks for a^2 + 2 b^4.

This certifies finite modular counts and an abstract local-law gap detector.
It does not prove infinitely many ascents or any new prime-gap theorem.
Standard library only. Run: python verify.py --output results.json
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction
from math import isqrt
from pathlib import Path


def primes_to(n: int) -> list[int]:
    if n < 2:
        return []
    flags = bytearray(b'\x01') * (n + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p*p::p] = b'\x00' * ((n - p*p)//p + 1)
    return [p for p in range(2, n + 1) if flags[p]]


def count_zeros(m: int, coefficient: int = 2) -> int:
    """Count (a,b) modulo m with a^2 + coefficient*b^4 == 0.
    Residue histograms avoid a quadratic scan through all input pairs.
    """
    squares = [0] * m
    for a in range(m):
        squares[a*a % m] += 1
    return sum(squares[-coefficient * pow(b, 4, m) % m]
               for b in range(m))


def rational_window(numerators_denominators, bits: int = 96):
    scale = 1 << bits
    count = 0
    lower = 0
    for numerator, denominator in numerators_denominators:
        lower += numerator * scale // denominator
        count += 1
    return lower, lower + count, scale


def direct_ratio(primes: list[int], r: int) -> Fraction:
    """Exact adjacent elementary-symmetric ratio; only for small examples."""
    e = [Fraction(0) for _ in range(r + 1)]
    e[0] = Fraction(1)
    for p in primes:
        w = Fraction(2, p)
        for j in range(r, 0, -1):
            e[j] += w * e[j-1]
    if r < 1 or not e[r]:
        raise ValueError('Unsupported rank')
    return e[r-1] / e[r]


def run() -> dict:
    all_p = primes_to(20000)
    local_rows = []
    for p in [p for p in all_p if 2 < p <= 199]:
        split = p % 8 in (1, 3)
        n1 = count_zeros(p)
        n2 = count_zeros(p*p)
        expected1 = 2*p - 1 if split else 1
        expected2 = 3*p*p - 2*p if split else p*p
        assert n1 == expected1, (p, n1, expected1)
        assert n2 == expected2, (p, n2, expected2)
        g1, g2 = Fraction(n1, p*p), Fraction(n2, p**4)
        eta = (g1 - g2) / (1 - g2)
        expected_eta = Fraction(2, p+2) if split else Fraction(0)
        assert eta == expected_eta, (p, eta, expected_eta)
        if split:
            assert eta/(1-eta) == Fraction(2, p)
        local_rows.append({'p': p, 'split': split, 'zeros_mod_p': n1,
                           'zeros_mod_p2': n2, 'eta': str(eta)})

    split_p = [p for p in all_p if p > 2 and p % 8 in (1, 3)]
    scale = 1 << 96
    lo = 0
    crossing = None
    for i, p in enumerate(split_p):
        lo += 4*p*scale // ((p+8)*(p+4))
        if lo > 2*scale:
            crossing = {'last_summed_prime': p,
                        'next_split_prime': split_p[i+1],
                        'number_of_terms': i+1, 'scale': str(scale),
                        'lower_numerator': str(lo),
                        'upper_numerator': str(lo+i+1),
                        'lower_margin_over_two': str(lo-2*scale),
                        'approximate_sum': lo/scale}
            break
    if crossing is None:
        raise RuntimeError('Search range did not certify a crossing')
    assert crossing['last_summed_prime'] == 3433
    assert crossing['next_split_prime'] == 3449

    # Independently test the coefficient-ratio signs with exact fractions.
    examples = []
    for p in (3449, 3691, 3929, 4001, 4049):
        i = split_p.index(p)
        q = split_p[i+1]
        prefix = split_p[:i]
        ml, mu, Q = rational_window((8, ell+8) for ell in prefix)
        assert ml//Q == mu//Q
        r = ml//Q
        ratio = direct_ratio(prefix, r)
        assert Fraction(2) < ratio <= 4
        gap = q-p
        ascent = ratio > Fraction(gap, 2)+1
        assert ascent == (gap == 2)
        examples.append({'p': p, 'q': q, 'gap': gap, 'rank_k': r+1,
                         'ratio_approx': float(ratio), 'ascent_exact': ascent,
                         'exact_ratio_numerator': str(ratio.numerator),
                         'exact_ratio_denominator': str(ratio.denominator)})

    return {'status': 'local counts and calibration only; no ascent supply proved',
            'coefficient': 2,
            'local_primes_checked': len(local_rows), 'local_results': local_rows,
            'rank_window_certificate': crossing,
            'exact_fraction_examples': examples}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('results.json'))
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    summary = {key: result[key] for key in ('status', 'local_primes_checked',
                                           'rank_window_certificate')}
    summary['examples'] = [{k: v for k,v in e.items() if not k.startswith('exact_ratio')}
                           for e in result['exact_fraction_examples']]
    print(json.dumps(summary, indent=2))
