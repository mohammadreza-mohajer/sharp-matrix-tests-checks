# Formalization scope and theorem map

The project has 33 theorem declarations in six modules, checked with Lean 4.19.0 and the pinned Mathlib v4.19.0 sources. Every declaration appears in `lean/Audit.lean` and `results/lean/axioms.txt`.

## Correspondence with the manuscript

| Paper statement | Lean declarations | Precise coverage |
| --- | --- | --- |
| Lemma 8.5, weighted monic division | `weighted_power_formula`, `weighted_quadratic_nilpotent`, `weighted_implies_two_level`, `monic_relation_to_quadratic`, `weighted_relation_nilpotent`, `weighted_monic_division` | Complete proof of the algebraic lemma over an arbitrary commutative ring, with nilpotence and weighted-coefficient hypotheses displayed |
| Theorem 8.6, ramified lower-bound argument | `matrix_nilpotent_of_weighted_annihilator`, `matrix_nilpotent_of_weighted_charpoly`, `matrix_translation_power` | Proves the passage from the weighted characteristic polynomial to the matrix power identity, using the actual Mathlib Cayley-Hamilton theorem |
| Theorem 8.6, double-root detecting identity | `square_zero_power`, `detecting_witness_double_root`, `detecting_witness_fixed_root` | Arbitrary-exponent binomial identity in rings with square-zero elements and the two block evaluations of the witness, with explicit inverse witnesses |
| Theorem 8.3, integral comparison | `hermite_value`, `hermite_value_at_one`, `normalized_derivative_factor`, `hermite_normalized_derivative` | All three normalized coordinate formulas in arbitrary commutative rings, including the factor k*zeta in the derivative coordinate |
| Theorem 8.3, nontrivial Smith block | `smith_block_reduction`, `smith_left_inverse`, `smith_right_inverse`, `smith_change_determinants`, `smith_diagonal_divisibility` | Explicit unimodular equivalence of the block [[pi*u,0],[pi,pi^2]] with diag(pi,pi^2*u), including inverses of both changes of basis |
| Proposition 7.1, coefficient pairing | `coefficient_gram_determinant` | Symbolic rank-three Gram determinant over every commutative ring |
| Theorems 7.5 and 8.7, period matrices | `kummer_period_invariance`, `kummer_period_determinant`, `artin_matrix_factorization`, `artin_matrix_determinant_ne_zero`, `tate_dual_evaluation` | General transformation identity, determinant, arbitrary-rank weighted Vandermonde invertibility, and inverse-transpose evaluation |
| Proposition 8.9 and Theorem 8.10, elliptic tensor | `elliptic_period_invariance`, `elliptic_period_determinant`, `mixed_tensor_period_invariance` | Symbolic elliptic transformation and tensor compatibility for arbitrary nonzero scalar parameters |
| Proposition 5.2, Sylvester splitting | `upper_shear_inverse`, `sylvester_block_change`, `sylvester_splits_extension` | General block conjugation for arbitrary finite block sizes; no sample-size restriction |

## Weighted coefficients

For i<n the Lean predicate is

```text
exists q : Nat, pi^q divides a_i and n <= i + k*q.
```

When k>0 this expresses exactly the existence of a divisibility exponent at least ceil((n-i)/k). The theorem constructs the monic polynomial as X^n plus its n lower coefficients. It proves divisibility of X^(p*k) in the polynomial ring itself by passing to the quotient by that monic polynomial.

The root proof first shows that x^(2k) has the form pi*b*x^k + pi^2*c. A general induction proves the weighted power formula, and pi^(p-1)=0 then gives x^(p*k)=0. This is a uniform proof for all parameters, rather than a finite enumeration.

The characteristic-p matrix theorem assumes a prime p and the displayed weighted characteristic polynomial for U-I. It proves U^(p^(j+1))=I. Identifying that characteristic polynomial from the spectrum of a continuous p-adic representation remains a written argument of the manuscript.

## Arithmetic inputs supplied by the paper

The formalization does not construct the local fields Q_p(zeta), their integer rings, continuous affine-group representations, the spectral classification, or the valuation-theoretic interpretation of exact denominators. Consequently the complete optimal-dimension classification is not asserted as one fully formalized Lean theorem.

The Hermite formulas and the Smith block are proved symbolically. The full cokernel isomorphism over the cyclotomic integer ring and the ramified derivative contribution are supplied by the manuscript's module argument and tested independently by the Python Smith computation.

The period formalization proves the stated algebraic matrix identities and arbitrary-rank invertibility. It does not construct Fontaine's period rings, unramified periods, the elliptic Tate module, Galois descent, Hodge filtrations, local duality, analytic distribution spaces, or convergence. The Artin Vandermonde theorem proves invertibility, while its Galois interpretation is supplied by the paper.

The Sylvester basis change is completely formalized as a matrix identity. The measure-valued extension, exact defect modules, and regulator reconstruction are outside that matrix calculation.

## Logical dependencies and integrity

The project introduces no custom axioms. The dependency audit checks every theorem and permits only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. There are no proof placeholders or `native_decide` invocations in these sources. Tactic-produced proof terms are checked by Lean.

`results/lean/status.json` records the compiler version, Mathlib commit, hashes of every source and configuration file, all theorem names, and all axiom dependencies. Python outputs record their program hashes and the citation metadata from paper_reference.json. Its manuscript hash is explicitly a historical reference; the public checks do not recompute a manuscript hash.

## Novelty and attribution

Formal verification establishes the declared mathematical statements. It does not certify research priority. The paper and `LITERATURE_COMPARISON.md` contain the mathematical attribution and focused originality assessment. Polynomial quotient arguments, Hermite interpolation, Smith reduction, Sylvester conjugation, Vandermonde determinants, and the basic period ingredients have classical antecedents. The paper's focused detecting-dimension results and associated lattice families are distinguished there.
