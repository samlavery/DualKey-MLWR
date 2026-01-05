require import AllCore Distr DBool List IntDiv Real RealExp FMap.
require import StdOrder StdBigop.
import RealOrder IntOrder.

require DualPKSig_Base.
import DualPKSig_Base.

require DualPKSig_LinearAlgebra.
import DualPKSig_LinearAlgebra.

(* Test: Can we define a module with Rq_vec variable? *)

(* Bijection operators *)
op real_to_sim_nonce (R : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) : Rq_vec =
  vec_add R (mask_at_zeros (scalar_vec_mul c X) P).

op sim_to_real_nonce (R' : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) : Rq_vec =
  vec_sub R' (mask_at_zeros (scalar_vec_mul c X) P).

(* Bijection lemmas *)
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

axiom apply_zeros_absorbs_nonzero (R X : Rq_vec) (P : zero_pos) (c : challenge) :
  apply_zeros (vec_add R (scalar_vec_mul c X)) P =
  apply_zeros (vec_add R (mask_at_zeros (scalar_vec_mul c X) P)) P.

module type DummyT = {
  proc init() : unit
}.

module Dummy : DummyT = {
  proc init() : unit = { }
}.

module TestMod (D : DummyT) = {
  var x : Rq_vec

  proc sign_real() : Rq_vec = {
    var r : Rq_vec;
    r <$ dT_vec w_R;
    return r;
  }

  proc sign_sim() : Rq_vec = {
    var r : Rq_vec;
    r <$ dT_vec w_R;
    return r;
  }
}.

module TM = TestMod(Dummy).
