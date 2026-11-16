"""Exact finite search for cyclotomic companion detectors over Z_p[zeta_p]."""
import argparse
import hashlib
import json
import math
from functools import lru_cache
from pathlib import Path
from time import perf_counter

from verification_context import paper_reference

ROOT = Path(__file__).resolve().parent

def search(p, d, e, limit=None):
    modulus = p ** e
    dimension = p - 1
    zero = (0,) * dimension
    one = (1,) + (0,) * (dimension - 1)
    def add(a, b):
        return tuple((x + y) % modulus for x, y in zip(a, b))
    def neg(a):
        return tuple(-x % modulus for x in a)
    @lru_cache(maxsize=None)
    def mul(a, b):
        values = [0] * (2 * dimension - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                values[i+j] += x*y
        for index in range(len(values)-1, dimension-1, -1):
            coefficient = values[index]
            if coefficient:
                for j in range(dimension):
                    values[index-dimension+j] -= coefficient
        return tuple(v % modulus for v in values[:dimension])
    def zeta_power(exponent):
        result = one
        generator = ((0,1)+(0,)*(dimension-2)) if p > 2 else (-1 % modulus,)
        for _ in range(exponent):
            result = mul(result, generator)
        return result
    def factor_times(poly, degree, root):
        result = [zero] * (len(poly)+degree)
        for i, coefficient in enumerate(poly):
            result[i] = add(result[i], neg(mul(root, coefficient)))
            result[i+degree] = add(result[i+degree], coefficient)
        return tuple(result)
    def remainder_nonzero(poly):
        values = [zero] * (p**d+1)
        values[0] = neg(one)
        values[-1] = one
        degree = len(poly)-1
        for j in range(len(values)-1, degree-1, -1):
            coefficient = values[j]
            if coefficient != zero:
                for i in range(degree):
                    values[j-degree+i] = add(values[j-degree+i], neg(mul(coefficient,poly[i])))
                values[j] = zero
        return any(value != zero for value in values[:degree])
    j = max(0,d-e)
    bound = min(p**max(0,d-e+1)+1,2*p**j+1) if e <= d else 2
    if limit is not None:
        bound = min(bound, limit)
    factors = [(1,one,"Z-1")]
    t = 1
    while p**(t-1) <= bound:
        for ell in range(1,p):
            factors.append((p**(t-1),zeta_power(ell),f"Z^{p**(t-1)}-zeta^{ell}"))
        t += 1
    tested = 0
    by_degree = {}
    started = perf_counter()
    def candidates(index, remaining, poly, multiplicities):
        if index == len(factors):
            if remaining == 0:
                yield poly, multiplicities
            return
        degree, root, _ = factors[index]
        current = poly
        for count in range(remaining//degree+1):
            yield from candidates(index+1, remaining-count*degree, current, multiplicities+(count,))
            if count < remaining//degree:
                current = factor_times(current,degree,root)
    for degree in range(1,bound+1):
        level = 0
        for polynomial, multiplicities in candidates(0,degree,(one,),()):
            tested += 1
            level += 1
            if remainder_nonzero(polynomial):
                by_degree[str(degree)] = level
                return {
                    "p":p,"d":d,"e":e,"minimum_dimension":degree,
                    "search_upper_bound":bound,"candidates_tested":tested,
                    "candidate_counts_through_first_witness":by_degree,
                    "witness_factors":[{"factor":factors[i][2],"multiplicity":m}
                        for i,m in enumerate(multiplicities) if m],
                    "elapsed_seconds":round(perf_counter()-started,3),
                }
        by_degree[str(degree)] = level
    return {"p":p,"d":d,"e":e,"minimum_dimension":None,"search_upper_bound":bound,
            "candidates_tested":tested,"candidate_counts_through_first_witness":by_degree,
            "elapsed_seconds":round(perf_counter()-started,3)}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--p",type=int,default=3)
    parser.add_argument("--d",type=int,default=2)
    parser.add_argument("--e",type=int,default=1)
    args=parser.parse_args()
    if args.p < 3 or any(args.p % q == 0 for q in range(2,math.isqrt(args.p)+1)) or args.d < 1 or args.e < 1:
        raise ValueError("Use an odd prime p and positive d,e.")
    result=search(args.p,args.d,args.e)
    result["method"]="Exhaustive monic cyclotomic-factor search with arithmetic modulo p^e."
    result["scope"]="Exact finite divisibility search; the paper proves the reduction from representations."
    result["paper_reference"] = paper_reference()
    result["script_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    destination=ROOT/f"cyclotomic_search_p{args.p}_d{args.d}_e{args.e}.json"
    destination.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result))
if __name__=="__main__":
    main()

