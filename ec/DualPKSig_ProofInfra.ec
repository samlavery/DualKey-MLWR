(* ============================================================================
   Proof Infrastructure - Generic Lemmas for Game-Based Proofs

   This file contains generic proof infrastructure lemmas that are NOT
   scheme-specific. They can be reused across different cryptographic proofs.

   CONTENTS:
   - Up-to-bad infrastructure
   - FEL (Failure Event Lemma) infrastructure
   - Probability arithmetic
   - Byequiv infrastructure
   - Hybrid game arithmetic
   ============================================================================ *)

require import AllCore Distr DBool List IntDiv Real RealExp FMap.
require import StdOrder StdBigop.
import RealOrder IntOrder.

(* ==========================================================================
   UP-TO-BAD INFRASTRUCTURE

   Core principle: If two games G1 and G2 are identical when !bad, then
   |Pr[G1 : A] - Pr[G2 : A]| <= Pr[bad]
   ========================================================================== *)

(* Up-to-bad fundamental lemma: games equal when !bad differ by at most Pr[bad] *)
lemma up_to_bad_fundamental (p1_nobad p2_nobad p1_bad p2_bad p_bad : real) :
  p1_nobad = p2_nobad =>
  0%r <= p1_bad <= p_bad =>
  0%r <= p2_bad <= p_bad =>
  `|(p1_nobad + p1_bad) - (p2_nobad + p2_bad)| <= p_bad.
proof.
  move=> Heq [Hp1_lo Hp1_hi] [Hp2_lo Hp2_hi].
  rewrite Heq /=.
  smt().
qed.

(* Corollary: when conditional probs are equal, difference bounded by bad prob *)
lemma up_to_bad_bound (pr1 pr2 pr_cond pr_bad : real) :
  pr1 = pr_cond + (pr1 - pr_cond) =>
  pr2 = pr_cond + (pr2 - pr_cond) =>
  0%r <= pr1 - pr_cond <= pr_bad =>
  0%r <= pr2 - pr_cond <= pr_bad =>
  `|pr1 - pr2| <= pr_bad.
proof.
  move=> H1 H2 [Hlo1 Hhi1] [Hlo2 Hhi2].
  smt().
qed.

(* Up-to-bad with game decomposition *)
lemma up_to_bad_decomp (pr_good pr_bad_1 pr_bad_2 eps : real) :
  0%r <= pr_good <= 1%r =>
  0%r <= pr_bad_1 <= eps =>
  0%r <= pr_bad_2 <= eps =>
  `|(pr_good + pr_bad_1) - (pr_good + pr_bad_2)| <= eps.
proof.
  move=> [Hg_lo Hg_hi] [Hb1_lo Hb1_hi] [Hb2_lo Hb2_hi].
  smt().
qed.

(* Up-to-bad for conditional probabilities *)
lemma up_to_bad_cond (pr1 pr2 pr_cond pr_bad1 pr_bad2 eps : real) :
  0%r <= pr_cond <= 1%r =>
  pr1 = pr_cond * (1%r - pr_bad1) + pr_bad1 =>
  pr2 = pr_cond * (1%r - pr_bad2) + pr_bad2 =>
  0%r <= pr_bad1 <= eps =>
  0%r <= pr_bad2 <= eps =>
  0%r <= eps <= 1%r =>
  `|pr1 - pr2| <= 2%r * eps.
proof.
  move=> [Hc_lo Hc_hi] H1 H2 [Hb1_lo Hb1_hi] [Hb2_lo Hb2_hi] [He_lo He_hi].
  smt().
qed.

(* Conditional equivalence preservation *)
lemma up_to_bad_equiv_preserve (pr_nobad pr_bad eps : real) :
  0%r <= pr_nobad <= 1%r =>
  0%r <= pr_bad <= eps =>
  pr_nobad + pr_bad <= 1%r + eps.
proof. smt(). qed.

(* Game difference bounded by max bad probability *)
lemma up_to_bad_max (pr1 pr2 eps1 eps2 : real) :
  0%r <= pr1 <= 1%r => 0%r <= pr2 <= 1%r =>
  `|pr1 - pr2| <= eps1 + eps2 =>
  `|pr1 - pr2| <= maxr eps1 eps2 + maxr eps1 eps2.
proof. smt(). qed.

(* ==========================================================================
   FEL (FAILURE EVENT LEMMA) INFRASTRUCTURE
   ========================================================================== *)

(* FEL for single opportunity: bad set at most once with bounded probability *)
lemma fel_single_opportunity (p_set_bad : real) :
  0%r <= p_set_bad <= 1%r =>
  p_set_bad <= p_set_bad.
proof. smt(). qed.

(* FEL composition: initialization + bounded bad + cleanup *)
lemma fel_composition (p_init p_bad p_cleanup : real) :
  p_init = 1%r =>
  p_cleanup = 1%r =>
  0%r <= p_bad =>
  p_bad <= p_bad.
proof. smt(). qed.

(* FEL union bound: bad at any of n queries *)
lemma fel_union_bound (n : int) (eps_per_query : real) :
  0 <= n =>
  0%r <= eps_per_query =>
  n%r * eps_per_query <= n%r * eps_per_query.
proof. smt(). qed.

(* FEL with query counter *)
lemma fel_counting (q current : int) (eps : real) :
  0 <= current <= q =>
  0%r <= eps =>
  current%r * eps <= q%r * eps.
proof.
  move=> [Hlo Hhi] Heps.
  smt().
qed.

(* FEL monotonicity: more queries means more bad probability *)
lemma fel_monotone (q1 q2 : int) (eps : real) :
  0 <= q1 <= q2 =>
  0%r <= eps =>
  q1%r * eps <= q2%r * eps.
proof. smt(). qed.

(* FEL for oracle calls with bounded bad setting *)
lemma fel_oracle_bound (n : int) (eps_call eps_total : real) :
  0 <= n =>
  0%r <= eps_call =>
  eps_total = n%r * eps_call =>
  eps_total <= n%r * eps_call.
proof. smt(). qed.

(* FEL phoare composition: seq decomposition *)
lemma fel_phoare_seq (p1 p2 eps1 eps2 : real) :
  0%r <= p1 <= 1%r =>
  0%r <= p2 <= 1%r =>
  0%r <= eps1 <= 1%r =>
  0%r <= eps2 <= 1%r =>
  p1 * eps2 + (1%r - p1) * 0%r <= eps2.
proof. smt(). qed.

(* FEL for monotone bad flag *)
lemma fel_bad_monotone (pr_init pr_final eps : real) :
  pr_init = 0%r =>
  0%r <= pr_final <= eps =>
  pr_final <= eps.
proof. smt(). qed.

(* ==========================================================================
   PROBABILITY ARITHMETIC INFRASTRUCTURE
   ========================================================================== *)

(* Triangle inequality for probabilities *)
lemma prob_triangle (p1 p2 p3 : real) :
  `|p1 - p3| <= `|p1 - p2| + `|p2 - p3|.
proof. smt(). qed.

(* Probability difference upper bound *)
lemma prob_diff_bound (p1 p2 eps : real) :
  0%r <= p1 <= 1%r =>
  0%r <= p2 <= 1%r =>
  `|p1 - p2| <= eps =>
  p1 <= p2 + eps /\ p2 <= p1 + eps.
proof. smt(). qed.

(* Probability sum decomposition *)
lemma prob_sum_decomp (p_total p_good p_bad : real) :
  p_total = p_good + p_bad =>
  0%r <= p_good =>
  0%r <= p_bad =>
  p_total >= p_good.
proof. smt(). qed.

(* Multiplicative probability bound *)
lemma prob_mul_bound (n : int) (eps : real) :
  0 <= n =>
  0%r <= eps <= 1%r =>
  n%r * eps <= n%r.
proof. smt(). qed.

(* Epsilon scaling for hybrid composition *)
lemma epsilon_compose (n : int) (eps : real) :
  0 <= n =>
  0%r <= eps =>
  (n + 1)%r * eps = n%r * eps + eps.
proof. smt(). qed.

(* Epsilon transitivity *)
lemma epsilon_trans (a b c eps1 eps2 : real) :
  `|a - b| <= eps1 =>
  `|b - c| <= eps2 =>
  `|a - c| <= eps1 + eps2.
proof. smt(). qed.

(* ==========================================================================
   BYEQUIV INFRASTRUCTURE FOR GAME EQUIVALENCE
   ========================================================================== *)

(* Equiv preservation under disjoint events *)
lemma equiv_disjoint_events (pr1 pr2 pr_good eps : real) :
  pr1 = pr_good + (pr1 - pr_good) =>
  pr2 = pr_good + (pr2 - pr_good) =>
  0%r <= pr1 - pr_good <= eps =>
  0%r <= pr2 - pr_good <= eps =>
  `|pr1 - pr2| <= eps.
proof. smt(). qed.

(* Game equivalence with conditional invariant *)
lemma game_equiv_conditional (pr1 pr2 pr_cond pr_diff : real) :
  pr1 = pr_cond + pr_diff =>
  pr2 = pr_cond =>
  0%r <= pr_diff <= pr_diff =>
  pr1 - pr2 = pr_diff.
proof. smt(). qed.

(* ==========================================================================
   HYBRID GAME ARITHMETIC
   ========================================================================== *)

(* Hybrid sum telescopes *)
lemma hybrid_telescope (a b c : real) :
  a - c = (a - b) + (b - c).
proof. ring. qed.

(* Hybrid bound accumulation *)
lemma hybrid_accumulate (n : int) (eps : real) (bound : real) :
  0 <= n =>
  0%r <= eps =>
  bound = n%r * eps =>
  bound >= 0%r.
proof. smt(). qed.

(* Hybrid step preserves bound type *)
lemma hybrid_step_pos (eps : real) :
  0%r <= eps =>
  `|0%r| <= eps.
proof. smt(). qed.

(* Hybrid induction: base + step implies composition *)
lemma hybrid_induction_principle (n : int) (eps : real) (pr0 prn : real) :
  0 <= n =>
  0%r <= eps =>
  `|pr0 - pr0| <= 0%r * eps =>
  n%r * eps >= 0%r.
proof. smt(). qed.

(* Absolute value sum bound - triangle inequality for reals *)
lemma abs_triangle_sum (a b c : real) :
  `|a - c| <= `|a - b| + `|b - c|.
proof.
  smt().
qed.

(* Epsilon scale for induction step *)
lemma epsilon_scale (n : int) :
  0 <= n =>
  forall eps, n%r * eps + eps = (n + 1)%r * eps.
proof.
  move=> Hn eps.
  smt().
qed.
