"""Independent exact tests of Lemma 8.5 over F_p[pi]/(pi^(p-1)).

This program implements the coefficient ring and monic remainders directly.
It does not import the other verification programs or reproduce a Lean proof.
"""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import itertools
import json
from pathlib import Path
import random

from verification_context import paper_reference

ROOT = Path(__file__).resolve().parent


class TruncatedRing:
    def __init__(self, p):
        self.p = p
        self.length = p - 1
        self.zero = (0,) * self.length
        self.one = (1,) + (0,) * (self.length - 1)
        self.pi = (0, 1) + (0,) * (self.length - 2)

    def add(self, a, b):
        return tuple((x + y) % self.p for x, y in zip(a, b))

    def neg(self, a):
        return tuple((-x) % self.p for x in a)

    def mul(self, a, b):
        result = [0] * self.length
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b[:self.length - i]):
                    result[i + j] = (result[i + j] + x * y) % self.p
        return tuple(result)

    def ideal_elements(self, q):
        if q >= self.length:
            return [self.zero]
        return [(0,) * q + digits for digits in itertools.product(range(self.p), repeat=self.length - q)]

    def random_ideal_element(self, q, rng):
        return tuple(0 if i < q else rng.randrange(self.p) for i in range(self.length))


def remainder(ring, polynomial, monic):
    degree = len(monic) - 1
    result = list(polynomial)
    while len(result) > degree:
        leading = result.pop()
        shift = len(result) - degree
        if leading != ring.zero:
            for i, coefficient in enumerate(monic[:-1]):
                result[i + shift] = ring.add(result[i + shift], ring.neg(ring.mul(leading, coefficient)))
    return result + [ring.zero] * (degree - len(result))


def multiply_mod(ring, a, b, monic):
    result = [ring.zero] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] = ring.add(result[i + j], ring.mul(x, y))
    return remainder(ring, result, monic)


def power_of_T(ring, exponent, monic):
    result = remainder(ring, [ring.one], monic)
    base = remainder(ring, [ring.zero, ring.one], monic)
    while exponent:
        if exponent & 1:
            result = multiply_mod(ring, result, base, monic)
        base = multiply_mod(ring, base, base, monic)
        exponent >>= 1
    return result


def run():
    counts = Counter()
    examples = []
    rng = random.Random(84613)
    for p, k in [(3, 1), (3, 2), (3, 3), (5, 1)]:
        ring = TruncatedRing(p)
        total = 0
        for n in range(1, 2 * k + 1):
            choices = [ring.ideal_elements((n - i + k - 1) // k) for i in range(n)]
            for coefficients in itertools.product(*choices):
                monic = list(coefficients) + [ring.one]
                if any(value != ring.zero for value in power_of_T(ring, p * k, monic)):
                    raise AssertionError((p, k, n, coefficients))
                counts["exhaustive_weighted_monic_division"] += 1
                total += 1
        examples.append({"p": p, "k": k, "monic_polynomials_exhausted": total})
    for p, k in [(5, 2), (7, 1), (7, 3)]:
        ring = TruncatedRing(p)
        for n in range(1, 2 * k + 1):
            for _ in range(40):
                coefficients = [ring.random_ideal_element((n - i + k - 1) // k, rng) for i in range(n)]
                if any(x != ring.zero for x in power_of_T(ring, p * k, coefficients + [ring.one])):
                    raise AssertionError((p, k, n, coefficients))
                counts["deterministic_sampled_weighted_monic_division"] += 1
    for p in (3, 5, 7):
        ring = TruncatedRing(p)
        for k in (1, 2, 3):
            monic = [ring.zero] * (2 * k) + [ring.one]
            monic[k] = ring.neg(ring.pi)
            if any(x != ring.zero for x in power_of_T(ring, p * k, monic)):
                raise AssertionError("Expected nilpotence")
            counts["sharp_weighted_exponent_vanishing"] += 1
            if not any(x != ring.zero for x in power_of_T(ring, (p - 1) * k, monic)):
                raise AssertionError("Expected nonzero earlier power")
            counts["sharp_weighted_exponent_nonvanishing"] += 1
        bad_constant = [ring.neg(ring.pi), ring.zero, ring.one]
        if not any(x != ring.zero for x in power_of_T(ring, p, bad_constant)):
            raise AssertionError("Missing quadratic weight was not detected")
        counts["counterexample_without_quadratic_coefficient_weight"] += 1
        bad_linear = [ring.zero, ring.neg(ring.one), ring.one]
        if not any(x != ring.zero for x in power_of_T(ring, p, bad_linear)):
            raise AssertionError("Missing linear weight was not detected")
        counts["counterexample_without_linear_coefficient_weight"] += 1
    return counts, examples


def main():
    started = datetime.now(timezone.utc).isoformat()
    try:
        counts, examples = run()
        status, error = "passed", None
    except Exception as exc:
        counts, examples = Counter(), []
        status, error = "failed", repr(exc)
    record = {
        "status": status, "started_utc": started,
        "finished_utc": datetime.now(timezone.utc).isoformat(),
        "method": "Exact truncated finite-ring arithmetic, exhaustive small cases, fixed-seed larger cases, and counterexamples to weakened hypotheses.",
        "check_count": sum(counts.values()), "checks_by_category": dict(counts),
        "exhaustive_examples": examples,
        "paper_reference": paper_reference(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Independent finite tests of the general theorem proved in Lean; not exhaustive over all primes or degrees.",
        "error": error,
    }
    (ROOT / "weighted_division_results.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": status, "check_count": sum(counts.values()), "categories": dict(counts), "error": error}))
    return 0 if status == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
