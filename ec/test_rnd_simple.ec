require import AllCore Distr DBool List IntDiv Real RealExp FMap.
require import StdOrder StdBigop.
import RealOrder IntOrder.

require DualPKSig_Base.
import DualPKSig_Base.

require DualPKSig_LinearAlgebra.
import DualPKSig_LinearAlgebra.

(* ==========================================================================
   SIMPLE RND TEST

   Test the rnd tactic with bijection coupling on nonce distributions.
   Uses abstract operators and axioms to avoid concrete type issues.
   ========================================================================== *)

(* The bijection functions for nonce coupling *)
op real_to_sim_nonce (R : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) : Rq_vec =
  vec_add R (mask_at_zeros (scalar_vec_mul c X) P).

op sim_to_real_nonce (R' : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) : Rq_vec =
  vec_sub R' (mask_at_zeros (scalar_vec_mul c X) P).

(* Bijection correctness *)
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

(* Axiom: apply_zeros removes the nonzero-position contribution *)
axiom apply_zeros_absorbs_nonzero (R X : Rq_vec) (P : zero_pos) (c : challenge) :
  apply_zeros (vec_add R (scalar_vec_mul c X)) P =
  apply_zeros (vec_add R (mask_at_zeros (scalar_vec_mul c X) P)) P.

(* ==========================================================================
   SIMPLIFIED GAMES - Modules need a parameter to have vars
   ========================================================================== *)

(* Dummy type for parameterizing modules *)
module type DummyT = {
  proc init() : unit
}.

module Dummy : DummyT = {
  proc init() : unit = { }
}.

(* Test games for rnd coupling - parameterized module can have vars *)
module TestGames (D : DummyT) = {
  var sk : Rq_vec
  var zpos : zero_pos
  var chal : challenge

  proc sign_real() : Rq_vec = {
    var R : Rq_vec;
    var S : Rq_vec;
    R <$ dT_vec w_R;
    S <- apply_zeros (vec_add R (scalar_vec_mul chal sk)) zpos;
    return S;
  }

  proc sign_sim() : Rq_vec = {
    var R' : Rq_vec;
    var S' : Rq_vec;
    R' <$ dT_vec w_R;
    S' <- apply_zeros R' zpos;
    return S';
  }
}.

module TG = TestGames(Dummy).

(* ==========================================================================
   THE KEY LEMMA: Response distribution equivalence via bijection

   Now in the section with the proper byequiv + rnd proof.
   ========================================================================== *)

section RndTest.

lemma oracle_equiv_rnd :
  equiv[TG.sign_real ~ TG.sign_sim :
        ={TG.sk, TG.zpos, TG.chal}
        ==> ={res}].
proof.
  proc.
  (* Couple nonce sampling using the bijection *)
  seq 1 1 : (={TG.sk, TG.zpos, TG.chal} /\
             R'{2} = real_to_sim_nonce R{1} TG.chal{1} TG.sk{1} TG.zpos{1}).
  - rnd (real_to_sim_nonce ^~ TG.chal{1} TG.sk{1} TG.zpos{1})
        (sim_to_real_nonce ^~ TG.chal{1} TG.sk{1} TG.zpos{1}).
    auto => /> &1 &2 Hsk Hp Hc.
    split.
    + (* Forward bijection *)
      move=> R' _.
      by rewrite nonce_bij_inverse.
    + (* Inverse bijection *)
      move=> R _.
      by rewrite nonce_bij_forward.
  (* Now show the responses are equal *)
  auto => /> &1 &2 Hsk Hp Hc HR'.
  (* Need: apply_zeros(R + c*X, P) = apply_zeros(R', P) where R' = R + mask(c*X, P) *)
  rewrite HR' /real_to_sim_nonce.
  by rewrite apply_zeros_absorbs_nonzero.
qed.

end section RndTest.
