require import AllCore Distr DBool List IntDiv Real RealExp FMap.
require import StdOrder StdBigop.
import RealOrder IntOrder.

require DualPKSig_Base.
import DualPKSig_Base.

require DualPKSig_LinearAlgebra.
import DualPKSig_LinearAlgebra.

require DualPKSig_Simulation.
import DualPKSig_Simulation.

(* Simplified oracle equivalence test using rnd *)
section TestRnd.

declare module A <: Adversary {-EUF_CMA, -G0_Sim, -SimState, -Sig}.

(* The bijection functions *)
op real_to_sim_nonce (R : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) : Rq_vec =
  vec_add R (mask_at_zeros (scalar_vec_mul c X) P).

op sim_to_real_nonce (R' : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) : Rq_vec =
  vec_sub R' (mask_at_zeros (scalar_vec_mul c X) P).

(* Bijection properties - will use axioms from LinearAlgebra *)
lemma nonce_bij_forward (R : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) :
  sim_to_real_nonce (real_to_sim_nonce R c X P) c X P = R.
proof.
  rewrite /sim_to_real_nonce /real_to_sim_nonce.
  exact: vec_add_sub_cancel.
qed.

lemma nonce_bij_inverse (R' : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) :
  real_to_sim_nonce (sim_to_real_nonce R' c X P) c X P = R'.
proof.
  rewrite /real_to_sim_nonce /sim_to_real_nonce.
  exact: vec_sub_add_cancel.
qed.

(* Response equivalence under bijection *)
lemma response_under_bijection (R : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) :
  let R' = real_to_sim_nonce R c X P in
  apply_zeros (vec_add R (scalar_vec_mul c X)) P =
  apply_zeros R' P.
proof.
  simplify.
  rewrite /real_to_sim_nonce.
  (* R' = R + mask(c*X, P), so we need:
     apply_zeros(R + c*X, P) = apply_zeros(R + mask(c*X, P), P)
     This is exactly apply_zeros_absorbs_nonzero *)
  by rewrite apply_zeros_absorbs_nonzero.
qed.

end section TestRnd.
