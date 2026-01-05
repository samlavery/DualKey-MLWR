(* ============================================================================
   Concrete Vector Algebra Instantiation via Clone

   This file clones the abstract VecAlgebra theory using the concrete proofs
   from DualPKSig_ConcreteAlgebra.ec, eliminating the axioms.
   ============================================================================ *)

require import AllCore List IntDiv.
require DualPKSig_VecTheory.
require DualPKSig_ConcreteAlgebra.

import DualPKSig_ConcreteAlgebra.

(* ==========================================================================
   Clone the abstract theory with concrete instantiation
   ========================================================================== *)

clone DualPKSig_VecTheory.VecAlgebra as ConcreteVec with
  type vec = Rq_vec_concrete,
  op zero = zero_vec_c,
  op add = vec_add_c,
  op neg = vec_neg_c,
  pred wf = wf_vec,
  pred reduced = reduced_vec
proof *.
  (* Prove each axiom using induction and smt *)

  realize add_comm.
    move=> a b.
    rewrite /vec_add_c.
    elim: a b => [|x xs IH] [|y ys] //=.
    have IH' := IH ys. rewrite /vec_add_c in IH'.
    by smt().
  qed.

  realize add_assoc.
    move=> a b c.
    rewrite /vec_add_c.
    elim: a b c => [|x xs IH] [|y ys] [|z zs] //=.
    have IH' := IH ys zs. rewrite /vec_add_c in IH'.
    by smt(mod_center_assoc).
  qed.

  realize add_zero_r.
    move=> v Hwf Hred.
    by apply vec_add_zero_r_c.
  qed.

  realize add_neg_cancel.
    move=> v Hwf.
    by apply vec_add_neg_cancel_c.
  qed.

  realize neg_neg.
    move=> v Hwf Hred.
    by apply vec_neg_neg_c.
  qed.

(* ==========================================================================
   Exported lemmas - these are now proven, not axioms
   ========================================================================== *)

lemma vec_add_comm : forall (a b : Rq_vec_concrete),
  vec_add_c a b = vec_add_c b a.
proof. by apply ConcreteVec.add_comm. qed.

lemma vec_add_assoc : forall (a b c : Rq_vec_concrete),
  vec_add_c (vec_add_c a b) c = vec_add_c a (vec_add_c b c).
proof. by apply ConcreteVec.add_assoc. qed.

lemma vec_add_zero_r : forall (v : Rq_vec_concrete),
  wf_vec v => reduced_vec v => vec_add_c v zero_vec_c = v.
proof. by apply ConcreteVec.add_zero_r. qed.

lemma vec_add_neg_cancel : forall (v : Rq_vec_concrete),
  wf_vec v => vec_add_c v (vec_neg_c v) = zero_vec_c.
proof. by apply ConcreteVec.add_neg_cancel. qed.

lemma vec_neg_neg : forall (v : Rq_vec_concrete),
  wf_vec v => reduced_vec v => vec_neg_c (vec_neg_c v) = v.
proof. by apply ConcreteVec.neg_neg. qed.

lemma vec_sub_is_add_neg : forall (a b : Rq_vec_concrete),
  vec_sub_c a b = vec_add_c a (vec_neg_c b).
proof. by apply ConcreteVec.sub_is_add_neg. qed.

print vec_add_comm.
print vec_add_assoc.
print vec_add_zero_r.
print vec_add_neg_cancel.
print vec_neg_neg.
print vec_sub_is_add_neg.
