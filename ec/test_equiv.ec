require import AllCore Distr.
require DualPKSig_Base DualPKSig_LinearAlgebra DualPKSig_Simulation.

import DualPKSig_Base DualPKSig_LinearAlgebra DualPKSig_Simulation.

(* Test: Can we prove output equality under bijection coupling? *)

(* The problem: response_structure shows that
   apply_zeros(sim_to_real(R', c, X, P) + c*X, P)
   = apply_zeros(R', P) + apply_zeros(nonzeros(c*X), P)
   = apply_zeros(R', P) + nonzeros(c*X, P)  [by mask_nonzeros_at_zeros]

   These are NOT equal unless nonzeros(c*X, P) = zero_vec.

   However, after round_vec p_s, they MIGHT be equal if the rounding
   absorbs the difference. But we removed those axioms as mathematically false.

   The real insight: the DISTRIBUTIONS are equal, but not pointwise values.
   This means we cannot prove eager_sim_oracle_equiv via simple coupling.

   Options:
   1. Keep as axiom (current approach)
   2. Use phoare to bound the probability difference (= 0)
   3. Restructure the proof differently
*)

(* Let's verify the distribution equality is properly established *)
lemma test_dist_equiv (X : Rq_vec) (P : zero_pos) (c : challenge) :
  dmap (dT_vec w_R) (fun R => round_vec p_s (apply_zeros (vec_add R (scalar_vec_mul c X)) P))
  = dmap (dT_vec w_R) (fun R' => round_vec p_s (apply_zeros R' P)).
proof.
  (* This follows from response_distribution_equiv by dmap composition *)
  have Hdist := response_distribution_equiv X P c.
  (* dmap (f ∘ g) = dmap f (dmap g) *)
  congr.
  exact: Hdist.
qed.
