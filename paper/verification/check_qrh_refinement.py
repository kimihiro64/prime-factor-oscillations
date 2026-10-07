"""Exact algebra checks for the source-dependent QRH refinement.

Run with Python 3. No third-party packages are required. This checks identities
and margins, not the analytic theorems of the cited OpenAI manuscript.
"""
from fractions import Fraction as F
from pathlib import Path
import json

# Polynomials in (delta, y), with exact rational coefficients.
def add(*polys):
    result = {}
    for poly in polys:
        for key, value in poly.items():
            result[key] = result.get(key, F(0)) + value
    return {key: value for key, value in result.items() if value}

def scale(poly, value):
    return {key: value * coefficient for key, coefficient in poly.items() if value * coefficient}

def mul(left, right):
    result = {}
    for (i, j), a in left.items():
        for (k, ell), b in right.items():
            key = (i + k, j + ell)
            result[key] = result.get(key, F(0)) + a * b
    return {key: value for key, value in result.items() if value}

def constant(value):
    return {(0, 0): F(value)}

def main():
    delta = {(1, 0): F(1)}
    y = {(0, 1): F(1)}
    v = add(constant(51), scale(y, 41))
    py = add(constant(7), scale(y, 18), scale(mul(y, y), 8))
    jy = add(constant(185), scale(y, 170),
             mul(delta, add(constant(-138), scale(y, 12), scale(mul(y, y), 96))))
    left = mul(v, add(
        scale(mul(jy, add(constant(1), mul(add(constant(3), scale(y, 8)), delta))), 2),
        scale(mul(mul(add(constant(F(5, 6)), scale(delta, -1)), delta), py), -468)))
    square_base = add(scale(mul(v, delta), 4), constant(-79))
    right = add(
        mul(add(constant(3), scale(y, 5)), add(mul(square_base, square_base), constant(49))),
        scale(mul(y, add(
            scale(mul(mul(v, delta), add(
                mul(mul(add(constant(1), scale(y, 3)),
                        add(constant(15), scale(y, 32))), delta),
                constant(9), scale(y, -13))), 4),
            constant(265), scale(y, 3485))), 4))
    assert left == right, "endpoint polynomial identity"

    t = F(1, 100000)
    ell = F(1, 6) + t
    b = F(1, 8)
    lx = (1 - ell - b) / 2
    ly = lx + b
    h = 1 + ell - lx
    signal_shift = lx / 2 - 1 + h / 6
    low = lx / 2 + b / 12
    boundary = low - signal_shift
    assert signal_shift == -F(11, 16)
    assert boundary == F(349999, 400000)
    assert lx + ly + ell == 1
    assert ell < F(1, 5)
    assert 1 - 3 * ell > 0
    assert lx - ell > 0
    assert ly - ell - 11 * b / 6 > 0
    assert ell / h > F(1, 5) > F(7, 37)

    margins = {
        "adaptive": F(49, 440640) - F(19, 8) * t,
        "floor": F(7, 1200) - 2 * t,
        "intermediate": F(49, 14400) - t,
        "small_rows": F(63, 800) - F(51, 100) * t,
        "principal_w": ly / 20,
        "principal_z": h / 600,
        "gram_length": ly - ell - 11 * b / 6,
    }
    assert all(value > 0 for value in margins.values())
    zeta_extension = min(F(1, 10000000), margins["adaptive"] / 8, (5 * ell - h) / 4)
    assert zeta_extension > 0
    assert margins["adaptive"] - 2 * zeta_extension > 0
    assert margins["floor"] - 2 * zeta_extension > 0

    x, w, z = F(87, 100), F(19, 20), F(33, 200)
    assert boundary > x
    assert 4 - 6 * x - 6 * z < 0
    good_terms = [4 - 6 * x - 6 * z, 1 - x - w - 6 * z,
                  -x - 6 * z, -x - w, -w - 6 * z]
    bad_terms = [1 - x - w, F(3, 2) - 3 * x, 2 - 3 * x - w,
                 2 - 4 * x, F(5, 2) - 4 * x - w, 3 - 6 * x,
                 4 - 6 * x - 6 * z]
    principal_terms = [-x, -6 * z, 4 - 5 * x - 6 * z, 1 - w - 6 * z]
    assert max(good_terms) == -F(181, 100)
    assert max(bad_terms) == -F(82, 100)
    assert max(principal_terms) == -F(87, 100)
    assert -1 - max(good_terms) > F(4, 5)

    result = {
        "status": "exact algebra checks passed",
        "scope": "Rational identities, margins, and endpoint polynomial certificate only.",
        "analytic_status": "Conditional on the explicitly cited source estimates; not independently certified here.",
        "lean_status": "Not formalized.",
        "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
        "boundary": str(boundary),
        "improvement_over_seven_eighths": str(F(7, 8) - boundary),
        "geometry": {key: str(value) for key, value in
                     {"t": t, "ell": ell, "b": b, "lx": lx, "ly": ly, "h": h}.items()},
        "positive_margins": {key: str(value) for key, value in margins.items()},
        "outer_extension": str(zeta_extension),
        "endpoint_polynomial_identity": True,
        "finite_numerics_used_as_asymptotic_proof": False,
    }
    destination = Path(__file__).resolve().with_name("qrh-refinement-check.json")
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
