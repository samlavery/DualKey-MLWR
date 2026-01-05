(* ============================================================================
   Hybrid Games for Simulation Proof

   This file contains:
   - Hybrid counter module
   - Bijection operators and lemmas
   - Distribution equivalence lemmas
   - HybridOracle and Hybrid game definitions
   - Response bad event handling
   ============================================================================ *)

require import AllCore Distr DBool List IntDiv Real RealExp FMap.
require import StdOrder StdBigop.
import RealOrder IntOrder.

require DualPKSig_Base.
import DualPKSig_Base.

require DualPKSig_LinearAlgebra.
import DualPKSig_LinearAlgebra.

require DualPKSig_RO.
import DualPKSig_RO.

require DualPKSig_ProofInfra.
import DualPKSig_ProofInfra.

require DualPKSig_IntermediateGames.
import DualPKSig_IntermediateGames.

(* ==========================================================================
   HYBRID COUNTER
   ========================================================================== *)

module HybridCount = {
  var count : int
  var qcount : int         (* Counts oracle calls (used for query bound) *)
  var switch : int
  var at_switch_real : bool  (* True = use real at switch, False = use sim at switch *)
  var bad : bool             (* Set when response_bad occurs at the switch point *)
  var bad_query : int        (* Query index where bad was set *)
  var bound_bad : bool       (* Set when adversary exceeds q_sign queries *)
}.

(* HYBRID PARAMETERIZATION:
   - H_i:     switch = i, at_switch_real = true  -> uses real at query i
   - H_{i+1}: switch = i, at_switch_real = false -> uses sim at query i

   This way consecutive hybrids differ only in a boolean, not in switch values,
   making pRHL proofs syntactically aligned. *)

(* ==========================================================================
   BIJECTION OPERATORS
   ========================================================================== *)

op real_to_sim_nonce (rv : Rq_vec) (c : challenge) (xv : Rq_vec) (p : zero_pos) : Rq_vec =
  vec_add rv (mask_at_zeros (scalar_vec_mul c xv) p).

op sim_to_real_nonce (rv' : Rq_vec) (c : challenge) (xv : Rq_vec) (p : zero_pos) : Rq_vec =
  vec_sub rv' (mask_at_zeros (scalar_vec_mul c xv) p).

(* Bijection correctness lemmas *)
lemma nonce_bij_forward (rv : Rq_vec) (c : challenge) (xv : Rq_vec) (p : zero_pos) :
  sim_to_real_nonce (real_to_sim_nonce rv c xv p) c xv p = rv.
proof.
  rewrite /sim_to_real_nonce /real_to_sim_nonce.
  exact: vec_add_sub_cancel.
qed.

lemma nonce_bij_inverse (rv' : Rq_vec) (c : challenge) (xv : Rq_vec) (p : zero_pos) :
  real_to_sim_nonce (sim_to_real_nonce rv' c xv p) c xv p = rv'.
proof.
  rewrite /real_to_sim_nonce /sim_to_real_nonce.
  exact: vec_sub_add_cancel.
qed.

(* Lambda form of bijection for rnd tactic compatibility *)
lemma nonce_bij_forward_lambda (c : challenge) (xv : Rq_vec) (p : zero_pos) (rv : Rq_vec) :
  (fun R' => sim_to_real_nonce R' c xv p) ((fun R => real_to_sim_nonce R c xv p) rv) = rv.
proof.
  simplify.
  exact: nonce_bij_forward.
qed.

lemma rnd_bij_forward_axiom (c : challenge) (xv : Rq_vec) (p : zero_pos) (rv : Rq_vec) :
  sim_to_real_nonce (real_to_sim_nonce rv c xv p) c xv p = rv.
proof. exact: nonce_bij_forward. qed.

lemma rnd_bij_forward_fun (c : challenge) (xv : Rq_vec) (p : zero_pos) :
  forall rv, (fun R' => sim_to_real_nonce R' c xv p) ((fun R => real_to_sim_nonce R c xv p) rv) = rv.
proof. move=> rv; simplify; exact: nonce_bij_forward. qed.

lemma rnd_bij_inverse_axiom (c : challenge) (xv : Rq_vec) (p : zero_pos) (rv' : Rq_vec) :
  real_to_sim_nonce (sim_to_real_nonce rv' c xv p) c xv p = rv'.
proof. exact: nonce_bij_inverse. qed.

lemma rnd_bij_inverse_fun (c : challenge) (xv : Rq_vec) (p : zero_pos) :
  forall rv', (fun R => real_to_sim_nonce R c xv p) ((fun R' => sim_to_real_nonce R' c xv p) rv') = rv'.
proof. move=> rv'; simplify; exact: nonce_bij_inverse. qed.

(* ==========================================================================
   DISTRIBUTION EQUIVALENCE LEMMAS
   ========================================================================== *)

(* Helper: vec_add is cancellative *)
lemma vec_add_cancel_r (a b c : Rq_vec) : vec_add a c = vec_add b c => a = b.
proof.
  move=> H.
  have H1 : vec_add (vec_add a c) (vec_neg c) = vec_add (vec_add b c) (vec_neg c)
    by rewrite H.
  have H2 : vec_add (vec_add a c) (vec_neg c) = a.
    by rewrite vec_add_assoc vec_add_neg_cancel vec_add_zero_r.
  have H3 : vec_add (vec_add b c) (vec_neg c) = b.
    by rewrite vec_add_assoc vec_add_neg_cancel vec_add_zero_r.
  by rewrite -H2 -H3.
qed.

(* Bijection lemma for vector addition *)
lemma vec_add_bij (v : Rq_vec) : bijective (fun x => vec_add x v).
proof.
  exists (fun x => vec_add x (vec_neg v)).
  split => x /=.
  - by rewrite vec_add_assoc vec_add_neg_cancel vec_add_zero_r.
  - rewrite vec_add_assoc.
    have H : vec_add (vec_neg v) v = zero_vec.
      by rewrite vec_add_comm vec_add_neg_cancel.
    by rewrite H vec_add_zero_r.
qed.

(* Shift-invariance of uniform distribution *)
lemma dT_vec_shift_invariant (v : Rq_vec) :
  dmap (dT_vec w_R) (fun R => vec_add R v) = dT_vec w_R.
proof.
  apply eq_funi_ll.
  - apply dmap_funi.
    + exact: (vec_add_bij v).
    + exact: dT_vec_funi.
  - by rewrite dmap_ll dT_vec_ll.
  - exact: dT_vec_funi.
  - exact: dT_vec_ll.
qed.

(* Shift-invariance for subtraction *)
lemma dT_vec_shift_sub_invariant (v : Rq_vec) :
  dmap (dT_vec w_R) (fun R => vec_sub R v) = dT_vec w_R.
proof.
  have H : dmap (dT_vec w_R) (fun R => vec_sub R v)
         = dmap (dT_vec w_R) (fun R => vec_add R (vec_neg v)).
    by congr; apply fun_ext => R; exact: vec_sub_is_add_neg.
  by rewrite H dT_vec_shift_invariant.
qed.

(* Bijection preserves uniform distribution (forward direction) *)
lemma bijection_preserves_uniform (c : challenge) (X : Rq_vec) (P : zero_pos) :
  dmap (dT_vec w_R) (fun R' => sim_to_real_nonce R' c X P) = dT_vec w_R.
proof.
  rewrite /sim_to_real_nonce.
  exact: dT_vec_shift_sub_invariant.
qed.

(* Bijection preserves uniform distribution (inverse direction) *)
lemma bijection_preserves_uniform_inv (c : challenge) (X : Rq_vec) (P : zero_pos) :
  dmap (dT_vec w_R) (fun R => real_to_sim_nonce R c X P) = dT_vec w_R.
proof.
  rewrite /real_to_sim_nonce.
  exact: dT_vec_shift_invariant.
qed.

(* Response distribution equivalence *)
lemma response_dist_equiv_lemma (X : Rq_vec) (P : zero_pos) (c : challenge) :
  dmap (dT_vec w_R) (fun R => apply_zeros (vec_add R (scalar_vec_mul c X)) P)
  = dmap (dT_vec w_R) (fun R' => apply_zeros R' P).
proof.
  have Step1 : dmap (dT_vec w_R) (fun R => apply_zeros (vec_add R (scalar_vec_mul c X)) P)
             = dmap (dmap (dT_vec w_R) (fun R => vec_add R (scalar_vec_mul c X)))
                    (fun R' => apply_zeros R' P)
    by rewrite dmap_comp.

  have Step2 : dmap (dT_vec w_R) (fun R => vec_add R (scalar_vec_mul c X)) = dT_vec w_R
    by exact: dT_vec_shift_invariant.

  by rewrite Step1 Step2.
qed.

(* ==========================================================================
   HYBRID ORACLE AND GAME
   ========================================================================== *)

module HybridOracle : OracleT = {
  proc sign(m : msg) : sig_t option = {
    var pk1, pk2 : Rp_vec;
    var lsigma : seed;
    var nonce_R, resp_S : Rq_vec;
    var u, sig_c : Rp_vec;
    var c : challenge;
    var zero_seed : seed;
    var zpos_P : zero_pos;
    var matY1_local : Rq_mat;

    (* Count oracle calls and flag overflow beyond q_sign *)
    if (q_sign <= HybridCount.qcount) {
      HybridCount.bound_bad <- true;
    }
    HybridCount.qcount <- HybridCount.qcount + 1;

    (pk1, pk2, lsigma) <- Sig.gpk;
    matY1_local <- Sig.matY1;
    EUF_CMA.qs <- m :: EUF_CMA.qs;

    zero_seed <- H1 pk1 pk2 m;
    zpos_P <- derive_zeros zero_seed;

    nonce_R <$ dT_vec w_R;
    c <$ dT_challenge w_c;

    (* Track bad event at the divergence point:
       At query count = switch, H_i (at_switch_real=true) uses real,
       while H_{i+1} (at_switch_real=false) uses sim.
       The bad event is when the real and simulated signatures would differ.
       This enables up-to-bad reasoning for the hybrid transition. *)
    if (HybridCount.count = HybridCount.switch) {
      if (response_bad nonce_R c Sig.gsk zpos_P) {
        HybridCount.bad <- true;
        HybridCount.bad_query <- HybridCount.count;
      }
    }

    (* HYBRID SWITCH with boolean at equality:
       - count < switch: use simulated (zero_vec)
       - count = switch: use real if at_switch_real, else sim
       - count > switch: use real

       NOTE: Both branches have identical structure (2 statements) to enable
       mechanical pRHL proofs. The sim branch uses zero_vec which equals
       the identity, so vec_add nonce_R zero_vec = nonce_R. *)
    if (HybridCount.count < HybridCount.switch) {
      (* Before switch: always sim *)
      resp_S <- vec_add nonce_R zero_vec;
      resp_S <- apply_zeros resp_S zpos_P;
    } else {
      if (HybridCount.count = HybridCount.switch) {
        (* At switch: behavior determined by at_switch_real boolean *)
        if (HybridCount.at_switch_real) {
          resp_S <- vec_add nonce_R (scalar_vec_mul c Sig.gsk);
          resp_S <- apply_zeros resp_S zpos_P;
        } else {
          resp_S <- vec_add nonce_R zero_vec;
          resp_S <- apply_zeros resp_S zpos_P;
        }
      } else {
        (* After switch: always real *)
        resp_S <- vec_add nonce_R (scalar_vec_mul c Sig.gsk);
        resp_S <- apply_zeros resp_S zpos_P;
      }
    }

    HybridCount.count <- HybridCount.count + 1;

    u <- u_of matY1_local nonce_R;
    sig_c <- sig_of resp_S zpos_P;
    return Some (u, sig_c);
  }
}.

(* ==========================================================================
   BOUNDED HYBRID ORACLE
   Structurally guarantees count < q_sign inside the oracle body.

   This wrapper checks count < q_sign at entry:
   - If count >= q_sign: returns None immediately (overflow case)
   - If count < q_sign: proceeds normally

   For bounded adversaries (A_bounded: qcount <= q_sign), the overflow
   case is never reached, so the games are equivalent. But EasyCrypt can
   now derive count < q_sign from the structural if-check.
   ========================================================================== *)

module BoundedHybridOracle : OracleT = {
  proc sign(m : msg) : sig_t option = {
    var pk1, pk2 : Rp_vec;
    var lsigma : seed;
    var nonce_R, resp_S : Rq_vec;
    var u, sig_c : Rp_vec;
    var c : challenge;
    var zero_seed : seed;
    var zpos_P : zero_pos;
    var matY1_local : Rq_mat;
    var result : sig_t option;

    result <- None;

    (* Count oracle calls and flag overflow beyond q_sign *)
    if (q_sign <= HybridCount.qcount) {
      HybridCount.bound_bad <- true;
    }
    HybridCount.qcount <- HybridCount.qcount + 1;

    (* BOUNDED CHECK: only proceed if count < q_sign *)
    if (HybridCount.count < q_sign) {
      (pk1, pk2, lsigma) <- Sig.gpk;
      matY1_local <- Sig.matY1;
      EUF_CMA.qs <- m :: EUF_CMA.qs;

      zero_seed <- H1 pk1 pk2 m;
      zpos_P <- derive_zeros zero_seed;

      nonce_R <$ dT_vec w_R;
      c <$ dT_challenge w_c;

      (* Track bad event at the divergence point *)
      if (HybridCount.count = HybridCount.switch) {
        if (response_bad nonce_R c Sig.gsk zpos_P) {
          HybridCount.bad <- true;
          HybridCount.bad_query <- HybridCount.count;
        }
      }

      (* HYBRID SWITCH with boolean at equality *)
      if (HybridCount.count < HybridCount.switch) {
        resp_S <- vec_add nonce_R zero_vec;
        resp_S <- apply_zeros resp_S zpos_P;
      } else {
        if (HybridCount.count = HybridCount.switch) {
          if (HybridCount.at_switch_real) {
            resp_S <- vec_add nonce_R (scalar_vec_mul c Sig.gsk);
            resp_S <- apply_zeros resp_S zpos_P;
          } else {
            resp_S <- vec_add nonce_R zero_vec;
            resp_S <- apply_zeros resp_S zpos_P;
          }
        } else {
          resp_S <- vec_add nonce_R (scalar_vec_mul c Sig.gsk);
          resp_S <- apply_zeros resp_S zpos_P;
        }
      }

      HybridCount.count <- HybridCount.count + 1;

      u <- u_of matY1_local nonce_R;
      sig_c <- sig_of resp_S zpos_P;
      result <- Some (u, sig_c);
    }

    return result;
  }
}.

(* Bounded version of Hybrid game using BoundedHybridOracle *)
module HybridBounded (A : Adversary) = {
  proc main(switch_point : int, use_real : bool) : bool = {
    var pk : pkey;
    var sk : skey;
    var sk_X : Rq_vec;
    var pk1_full, pk2_full : Rq_vec;
    var pk1, pk2 : Rp_vec;
    var m : msg;
    var s : sig_t;
    var valid : bool;

    HybridCount.count <- 0;
    HybridCount.qcount <- 0;
    HybridCount.switch <- switch_point;
    HybridCount.at_switch_real <- use_real;
    HybridCount.bad <- false;
    HybridCount.bad_query <- (-1);
    HybridCount.bound_bad <- false;
    EUF_CMA.qs <- [];

    Sig.gsigma <$ dseed;
    Sig.matY1 <- expand_matrix Sig.gsigma 1;
    Sig.matY2 <- expand_matrix Sig.gsigma 2;

    sk_X <$ dT_vec w_X;

    pk1_full <- mat_vec_mul Sig.matY1 sk_X;
    pk2_full <- mat_vec_mul Sig.matY2 sk_X;
    pk1 <- round_vec p_pk pk1_full;
    pk2 <- round_vec p_pk pk2_full;

    Sig.gpk <- (pk1, pk2, Sig.gsigma);
    Sig.gsk <- sk_X;

    pk <- Sig.gpk;
    sk <- Sig.gsk;

    (m, s) <@ A(BoundedHybridOracle).forge(pk);
    valid <@ Sig.verify(pk, m, s);

    HybridCount.bound_bad <- (q_sign < HybridCount.qcount);
    return valid /\ !(m \in EUF_CMA.qs);
  }
}.

(* ==========================================================================
   BOUNDED SIMULATION ORACLE
   Shares HybridCount.count with BoundedHybridOracle for equivalence proofs.
   ========================================================================== *)

module BoundedSimO : OracleT = {
  proc sign(m : msg) : sig_t option = {
    var pk1, pk2 : Rp_vec;
    var lsigma : seed;
    var nonce_R, resp_S : Rq_vec;
    var u, sig_c : Rp_vec;
    var c : challenge;
    var zero_seed : seed;
    var zpos_P : zero_pos;
    var matY1_local : Rq_mat;
    var result : sig_t option;

    result <- None;

    (* Count oracle calls and flag overflow beyond q_sign *)
    if (q_sign <= HybridCount.qcount) {
      HybridCount.bound_bad <- true;
    }
    HybridCount.qcount <- HybridCount.qcount + 1;

    (* BOUNDED CHECK: only proceed if count < q_sign *)
    if (HybridCount.count < q_sign) {
      (pk1, pk2, lsigma) <- SimState.gpk;
      matY1_local <- SimState.matY1;
      SimState.qs <- m :: SimState.qs;

      zero_seed <- H1 pk1 pk2 m;
      zpos_P <- derive_zeros zero_seed;

      nonce_R <$ dT_vec w_R;
      c <$ dT_challenge w_c;

      resp_S <- vec_add nonce_R zero_vec;
      resp_S <- apply_zeros resp_S zpos_P;

      HybridCount.count <- HybridCount.count + 1;

      u <- u_of matY1_local nonce_R;
      sig_c <- sig_of resp_S zpos_P;
      result <- Some (u, sig_c);
    }

    return result;
  }
}.

(* Counting simulation oracle (unbounded): tracks qcount for query bounds *)
module SimO_Count : OracleT = {
  proc sign(m : msg) : sig_t option = {
    var pk1, pk2 : Rp_vec;
    var lsigma : seed;
    var nonce_R, resp_S : Rq_vec;
    var u, sig_c : Rp_vec;
    var c : challenge;
    var zero_seed : seed;
    var zpos_P : zero_pos;
    var matY1_local : Rq_mat;

    (* Count oracle calls and flag overflow beyond q_sign *)
    if (q_sign <= HybridCount.qcount) {
      HybridCount.bound_bad <- true;
    }
    HybridCount.qcount <- HybridCount.qcount + 1;

    (pk1, pk2, lsigma) <- SimState.gpk;
    matY1_local <- SimState.matY1;
    SimState.qs <- m :: SimState.qs;

    zero_seed <- H1 pk1 pk2 m;
    zpos_P <- derive_zeros zero_seed;

    nonce_R <$ dT_vec w_R;
    c <$ dT_challenge w_c;

    resp_S <- vec_add nonce_R zero_vec;
    resp_S <- apply_zeros resp_S zpos_P;

    HybridCount.count <- HybridCount.count + 1;

    u <- u_of matY1_local nonce_R;
    sig_c <- sig_of resp_S zpos_P;
    return Some (u, sig_c);
  }
}.

(* Counting version of G0_Sim using SimO_Count *)
module G0_SimCount (A : Adversary) = {
  var gsk : skey

  proc main() : bool = {
    var sigma : seed;
    var sX : Rq_vec;
    var t1, t2 : Rp_vec;
    var m : msg;
    var s : sig_t;
    var valid : bool;
    var mY1, mY2 : Rq_mat;

    sigma <$ dseed;
    mY1 <- expand_matrix sigma 1;
    mY2 <- expand_matrix sigma 2;

    sX <$ dT_vec w_X;

    t1 <- round_vec p_pk (mat_vec_mul mY1 sX);
    t2 <- round_vec p_pk (mat_vec_mul mY2 sX);

    HybridCount.count <- 0;
    HybridCount.qcount <- 0;
    HybridCount.bad <- false;
    HybridCount.bad_query <- (-1);
    HybridCount.bound_bad <- false;
    SimState.qs <- [];

    SimState.gpk <- (t1, t2, sigma);
    SimState.matY1 <- mY1;
    SimState.matY2 <- mY2;
    gsk <- sX;

    (m, s) <@ A(SimO_Count).forge(SimState.gpk);
    valid <@ Sig.verify(SimState.gpk, m, s);

    HybridCount.bound_bad <- (q_sign < HybridCount.qcount);
    return valid /\ !(m \in SimState.qs);
  }
}.

(* Bounded version of G0_Sim game using BoundedSimO *)
module G0_SimBounded (A : Adversary) = {
  var gsk : skey

  proc main() : bool = {
    var sigma : seed;
    var sX : Rq_vec;
    var t1, t2 : Rp_vec;
    var m : msg;
    var s : sig_t;
    var valid : bool;
    var mY1, mY2 : Rq_mat;

    sigma <$ dseed;
    mY1 <- expand_matrix sigma 1;
    mY2 <- expand_matrix sigma 2;

    sX <$ dT_vec w_X;

    t1 <- round_vec p_pk (mat_vec_mul mY1 sX);
    t2 <- round_vec p_pk (mat_vec_mul mY2 sX);

    HybridCount.count <- 0;
    HybridCount.qcount <- 0;
    HybridCount.bad <- false;
    HybridCount.bad_query <- (-1);
    HybridCount.bound_bad <- false;
    SimState.qs <- [];

    SimState.gpk <- (t1, t2, sigma);
    SimState.matY1 <- mY1;
    SimState.matY2 <- mY2;
    gsk <- sX;

    (m, s) <@ A(BoundedSimO).forge(SimState.gpk);
    valid <@ Sig.verify(SimState.gpk, m, s);

    HybridCount.bound_bad <- (q_sign < HybridCount.qcount);
    return valid /\ !(m \in SimState.qs);
  }
}.

module Hybrid (A : Adversary) = {
  proc main(switch_point : int, use_real : bool) : bool = {
    var pk : pkey;
    var sk : skey;
    var sk_X : Rq_vec;
    var pk1_full, pk2_full : Rq_vec;
    var pk1, pk2 : Rp_vec;
    var m : msg;
    var s : sig_t;
    var valid : bool;

    HybridCount.count <- 0;
    HybridCount.qcount <- 0;
    HybridCount.switch <- switch_point;
    HybridCount.at_switch_real <- use_real;
    HybridCount.bad <- false;
    HybridCount.bad_query <- (-1);
    HybridCount.bound_bad <- false;
    EUF_CMA.qs <- [];

    Sig.gsigma <$ dseed;
    Sig.matY1 <- expand_matrix Sig.gsigma 1;
    Sig.matY2 <- expand_matrix Sig.gsigma 2;

    sk_X <$ dT_vec w_X;

    pk1_full <- mat_vec_mul Sig.matY1 sk_X;
    pk2_full <- mat_vec_mul Sig.matY2 sk_X;
    pk1 <- round_vec p_pk pk1_full;
    pk2 <- round_vec p_pk pk2_full;

    Sig.gpk <- (pk1, pk2, Sig.gsigma);
    Sig.gsk <- sk_X;

    pk <- Sig.gpk;
    sk <- Sig.gsk;

    (m, s) <@ A(HybridOracle).forge(pk);
    valid <@ Sig.verify(pk, m, s);

    HybridCount.bound_bad <- (q_sign < HybridCount.qcount);
    return valid /\ !(m \in EUF_CMA.qs);
  }
}.

(* ==========================================================================
   HYBRID HELPER LEMMAS
   ========================================================================== *)

lemma hybrid_oracle_real_branch :
  forall (c : int) (s : int), 0 <= c => s <= 0 => !(c < s).
proof. smt(). qed.

lemma hybrid_oracle_sim_branch :
  forall (c : int) (s : int), 0 <= c < s => c < s.
proof. smt(). qed.

lemma switch_zero_always_else :
  forall (count : int), 0 <= count => !(count < 0).
proof. smt(). qed.

lemma switch_qsign_always_if :
  forall (count : int), 0 <= count < q_sign => count < q_sign.
proof. smt(). qed.

(* ==========================================================================
   RESPONSE BAD EVENT LEMMAS
   ========================================================================== *)

lemma response_bad_equiv (R : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) :
  !response_bad R c X P =>
  round_vec p_s (apply_zeros (vec_add R (scalar_vec_mul c X)) P) =
  round_vec p_s (apply_zeros R P).
proof.
  by rewrite /response_bad => /negbNE.
qed.

lemma response_bad_bound (c : challenge) (X : Rq_vec) (P : zero_pos) :
  mu (dT_vec w_R) (fun R => response_bad R c X P) <= epsilon_round.
proof.
  exact: response_bad_prob.
qed.

lemma bad_flag_implies_sig_equal (R : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos) :
  !(round_vec p_s (apply_zeros (vec_add R (scalar_vec_mul c X)) P) <>
    round_vec p_s (apply_zeros R P)) =>
  round_vec p_s (apply_zeros (vec_add R (scalar_vec_mul c X)) P) =
  round_vec p_s (apply_zeros R P).
proof.
  by move=> /negbNE.
qed.

lemma bad_false_sig_equal (R : Rq_vec) (c : challenge) (X : Rq_vec) (P : zero_pos)
    (resp_real resp_sim : Rq_vec) :
  resp_real = apply_zeros (vec_add R (scalar_vec_mul c X)) P =>
  resp_sim = apply_zeros R P =>
  !(round_vec p_s resp_real <> round_vec p_s resp_sim) =>
  round_vec p_s resp_real = round_vec p_s resp_sim.
proof.
  by move=> -> -> /negbNE.
qed.

(* While loop termination probability *)
lemma while_loop_termination :
  forall (matY1 : Rq_mat) (pk1 : Rp_vec) (X : Rq_vec) (P : zero_pos) (c : challenge),
    mu (dT_vec w_R) (fun r =>
      sign_accept_r matY1 pk1 X P c r)
    >= 1%r - rejection_prob.
proof.
  move=> matY1 pk1 X P c.
  have Hll : is_lossless (dT_vec w_R) by exact: dT_vec_ll.
  have Hbound := rejection_probability_bound matY1 pk1 X P c.
  have Hmu_not := mu_not (dT_vec w_R)
    (fun r => !sign_accept_r matY1 pk1 X P c r).
  have Hpred : mu (dT_vec w_R)
      (predC (fun r => !sign_accept_r matY1 pk1 X P c r))
    = mu (dT_vec w_R)
      (fun r => sign_accept_r matY1 pk1 X P c r).
    congr; apply fun_ext => r; rewrite /predC /=; smt().
  rewrite -Hpred Hmu_not Hll; smt().
qed.
