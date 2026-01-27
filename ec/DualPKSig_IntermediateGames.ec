(* ============================================================================
   Intermediate Games for Simulation Proof

   This file contains:
   - Bad event tracking module
   - Rejection probability bound (exported)
   - Pure operators for deterministic computations
   - Congruence lemmas
   - Intermediate game definitions (EUF_CMA_Inline, EUF_CMA_NoLoop, etc.)
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

(* ==========================================================================
   CONGRUENCE LEMMAS for module state substitution in equiv proofs
   ========================================================================== *)

lemma mat_vec_mul_congr (M1 M2 : Rq_mat) (v1 v2 : Rq_vec) :
  M1 = M2 => v1 = v2 => mat_vec_mul M1 v1 = mat_vec_mul M2 v2.
proof. by move=> -> ->. qed.

lemma round_vec_congr p (x y : Rq_vec) :
  x = y => round_vec p x = round_vec p y.
proof. by move=> ->. qed.

(* ==========================================================================
   H2 ORACLE TYPE
   ========================================================================== *)

module type H2_OracleT = {
  proc init() : unit
  proc get(u : Rp_vec, pk1 : Rp_vec, m : msg) : challenge
  proc set(u : Rp_vec, pk1 : Rp_vec, m : msg, c : challenge) : unit
}.

(* ==========================================================================
   BAD EVENT TRACKING FOR FEL-BASED PROOF
   ========================================================================== *)

module BadEvent = {
  var bad : bool
  var qcount : int
}.

(* ==========================================================================
   REJECTION PROBABILITY BOUND (exported for use in DualPKSig.ec)
   ========================================================================== *)

op rejection_prob : real = 2%r ^ (-160%r).

(* Parameter axiom: rejection probability for the full sign_accept filter. *)
axiom rejection_probability_bound :
  forall (matY1 : Rq_mat) (pk1 : Rp_vec) (X : Rq_vec) (P : zero_pos) (c : challenge),
    mu (dT_vec w_R) (fun r =>
      !sign_accept_r matY1 pk1 X P c r)
    <= rejection_prob.

(* ==========================================================================
   PURE OPERATORS FOR DETERMINISTIC COMPUTATIONS
   Note: u_of and sig_of are imported from DualPKSig_Base
   ========================================================================== *)

(* Combined signature output *)
op sign_output (Y : Rq_mat) (R : Rq_vec) (resp_S : Rq_vec) (P : zero_pos) : sig_t option =
  Some (u_of Y R, sig_of resp_S P).

(* --------------------------------------------------------------------------
   CONGRUENCE LEMMAS: equal inputs => equal outputs
   Note: u_of_congr and sig_of_congr are imported from DualPKSig_Base
   -------------------------------------------------------------------------- *)

lemma sign_output_congr (Y1 Y2 : Rq_mat) (R1 R2 S1 S2 : Rq_vec) (P1 P2 : zero_pos) :
  Y1 = Y2 => R1 = R2 => S1 = S2 => P1 = P2 =>
  sign_output Y1 R1 S1 P1 = sign_output Y2 R2 S2 P2.
proof. by move=> -> -> -> ->. qed.

lemma output_pair_congr (Y1 Y2 : Rq_mat) (R1 R2 : Rq_vec) (S1 S2 : Rq_vec) (P1 P2 : zero_pos) :
  Y1 = Y2 => R1 = R2 => S1 = S2 => P1 = P2 =>
  Some (u_of Y1 R1, sig_of S1 P1) = Some (u_of Y2 R2, sig_of S2 P2).
proof. by move=> -> -> -> ->. qed.

(* MODULE_CONGRUENCE: Function application preserves module variable equality. *)
lemma module_congruence_sign_output :
  forall (matY1_1 matY1_2 : Rq_mat) (nonce_R : Rq_vec) (resp_S : Rq_vec) (P : zero_pos),
    matY1_1 = matY1_2 =>
    (round_vec p_pk (mat_vec_mul matY1_1 nonce_R),
     sig_of resp_S P) =
    (round_vec p_pk (mat_vec_mul matY1_2 nonce_R),
     sig_of resp_S P).
proof.
  move=> matY1_1 matY1_2 nonce_R resp_S P HY.
  by rewrite HY.
qed.

(* ==========================================================================
   EUF_CMA_INLINE - INTERMEDIATE GAME
   ========================================================================== *)

module EUF_CMA_Inline (A : Adversary) = {
  module O : OracleT = {
    proc sign(m : msg) : sig_t option = {
      var s : sig_t option;
      var pk1, pk2 : Rp_vec;
      var lsigma : seed;
      var nonce_R, resp_S, u_full, d_vec : Rq_vec;
      var u, sig_c : Rp_vec;
      var c : challenge;
      var zero_seed : seed;
      var zpos_P : zero_pos;
      var result : sig_t option;
      var valid : bool;
      var ctr : int;

      EUF_CMA.qs <- m :: EUF_CMA.qs;

      (pk1, pk2, lsigma) <- Sig.gpk;
      Sig.matY1 <- expand_matrix lsigma 1;
      Sig.matY2 <- expand_matrix lsigma 2;

      zero_seed <- H1 pk1 pk2 m;
      zpos_P <- derive_zeros zero_seed;

      ctr <- 0;
      valid <- false;
      result <- None;

      while (!valid /\ ctr < 256) {
        ctr <- ctr + 1;

        nonce_R <$ dT_vec w_R;
        u_full <- mat_vec_mul Sig.matY1 nonce_R;
        u <- round_vec p_pk u_full;

        if (u_distinct_ok u) {
          c <- H2 u pk1 m;

          resp_S <- vec_add nonce_R (scalar_vec_mul c Sig.gsk);
          d_vec <- scalar_vec_mul c Sig.gsk;

          if (sign_accept Sig.matY1 pk1 u_full u resp_S d_vec c zpos_P) {
            resp_S <- apply_zeros resp_S zpos_P;
            sig_c <- sig_of resp_S zpos_P;
            result <- Some (u, sig_c);
            valid <- true;
          }
        }
      }

      s <- result;
      return s;
    }
  }

  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var sk_X : Rq_vec;
    var pk1_full, pk2_full : Rq_vec;
    var pk1, pk2 : Rp_vec;
    var m : msg;
    var s : sig_t;
    var valid : bool;

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

    (m, s) <@ A(O).forge(pk);
    valid <@ Sig.verify(pk, m, s);

    return valid /\ !(m \in EUF_CMA.qs);
  }
}.

(* ==========================================================================
   EUF_CMA_NoLoop - No rejection sampling
   ========================================================================== *)

module EUF_CMA_NoLoop (A : Adversary) = {
  module O : OracleT = {
    proc sign(m : msg) : sig_t option = {
      var pk1, pk2 : Rp_vec;
      var lsigma : seed;
      var nonce_R, resp_S, d_vec, u_full : Rq_vec;
      var u, sig_c : Rp_vec;
      var c : challenge;
      var zero_seed : seed;
      var zpos_P : zero_pos;

      (pk1, pk2, lsigma) <- Sig.gpk;
      EUF_CMA.qs <- m :: EUF_CMA.qs;

      zero_seed <- H1 pk1 pk2 m;
      zpos_P <- derive_zeros zero_seed;

      nonce_R <$ dT_vec w_R;
      c <$ dT_challenge w_c;

      resp_S <- vec_add nonce_R (scalar_vec_mul c Sig.gsk);
      resp_S <- apply_zeros resp_S zpos_P;

      u <- round_vec p_pk (mat_vec_mul Sig.matY1 nonce_R);
      sig_c <- sig_of resp_S zpos_P;
      return Some (u, sig_c);
    }
  }

  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var sk_X : Rq_vec;
    var pk1_full, pk2_full : Rq_vec;
    var pk1, pk2 : Rp_vec;
    var m : msg;
    var s : sig_t;
    var valid : bool;

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

    (m, s) <@ A(O).forge(pk);
    valid <@ Sig.verify(pk, m, s);

    return valid /\ !(m \in EUF_CMA.qs);
  }
}.

(* ==========================================================================
   EUF_CMA_NoLoop_Bad - NoLoop with bad event tracking
   ========================================================================== *)

module EUF_CMA_NoLoop_Bad (A : Adversary) = {
  module O : OracleT = {
    proc sign(m : msg) : sig_t option = {
      var pk1, pk2 : Rp_vec;
      var lsigma : seed;
      var nonce_R, resp_S, d_vec, u_full : Rq_vec;
      var u, sig_c : Rp_vec;
      var c : challenge;
      var zero_seed : seed;
      var zpos_P : zero_pos;

      (pk1, pk2, lsigma) <- Sig.gpk;
      EUF_CMA.qs <- m :: EUF_CMA.qs;

      zero_seed <- H1 pk1 pk2 m;
      zpos_P <- derive_zeros zero_seed;

      nonce_R <$ dT_vec w_R;
      c <$ dT_challenge w_c;

      u_full <- mat_vec_mul Sig.matY1 nonce_R;
      u <- round_vec p_pk u_full;

      resp_S <- vec_add nonce_R (scalar_vec_mul c Sig.gsk);
      d_vec <- scalar_vec_mul c Sig.gsk;

      if (!(sign_accept Sig.matY1 pk1 u_full u resp_S d_vec c zpos_P)) {
        BadEvent.bad <- true;
      }
      BadEvent.qcount <- BadEvent.qcount + 1;

      resp_S <- apply_zeros resp_S zpos_P;
      sig_c <- sig_of resp_S zpos_P;
      return Some (u, sig_c);
    }
  }

  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var sk_X : Rq_vec;
    var pk1_full, pk2_full : Rq_vec;
    var pk1, pk2 : Rp_vec;
    var m : msg;
    var s : sig_t;
    var valid : bool;

    BadEvent.bad <- false;
    BadEvent.qcount <- 0;
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

    (m, s) <@ A(O).forge(pk);
    valid <@ Sig.verify(pk, m, s);

    return valid /\ !(m \in EUF_CMA.qs);
  }
}.

(* ==========================================================================
   EUF_CMA_Eager - Eager challenge sampling
   ========================================================================== *)

module EUF_CMA_Eager (A : Adversary) = {
  module O : OracleT = {
    proc sign(m : msg) : sig_t option = {
      var pk1, pk2 : Rp_vec;
      var lsigma : seed;
      var nonce_R, resp_S : Rq_vec;
      var u, sig_c : Rp_vec;
      var c : challenge;
      var zero_seed : seed;
      var zpos_P : zero_pos;

      (pk1, pk2, lsigma) <- Sig.gpk;
      EUF_CMA.qs <- m :: EUF_CMA.qs;

      zero_seed <- H1 pk1 pk2 m;
      zpos_P <- derive_zeros zero_seed;

      nonce_R <$ dT_vec w_R;
      c <$ dT_challenge w_c;

      resp_S <- vec_add nonce_R (scalar_vec_mul c Sig.gsk);
      resp_S <- apply_zeros resp_S zpos_P;

      u <- round_vec p_pk (mat_vec_mul Sig.matY1 nonce_R);
      sig_c <- sig_of resp_S zpos_P;
      return Some (u, sig_c);
    }
  }

  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var sk_X : Rq_vec;
    var pk1_full, pk2_full : Rq_vec;
    var pk1, pk2 : Rp_vec;
    var m : msg;
    var s : sig_t;
    var valid : bool;

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

    (m, s) <@ A(O).forge(pk);
    valid <@ Sig.verify(pk, m, s);

    return valid /\ !(m \in EUF_CMA.qs);
  }
}.
