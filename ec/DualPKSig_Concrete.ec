(* ============================================================================
   Dual Public Key Signature Scheme - Concrete Type Implementations

   Machine-checked proofs of algebraic properties:
   - vec_decomp: v = mask_zeros(v,P) + mask_nonzeros(v,P)
   - apply_zeros_mask_nonzeros: apply_zeros(mask_nonzeros(v,P),P) = mask_nonzeros(v,P)
   - apply_zeros_mask_zeros: apply_zeros(mask_zeros(v,P),P) = zero_vec
   - apply_zeros_linear: apply_zeros(a+b,P) = apply_zeros(a,P) + apply_zeros(b,P)
   ============================================================================ *)

require import AllCore Distr DBool List IntDiv Real RealExp.
require import StdOrder StdBigop.
import RealOrder IntOrder.

(* ==========================================================================
   SECTION 1: PARAMETERS
   ========================================================================== *)

op n : int = 128.
op k : int = 4.
op q : int = 4099.

lemma n_pos : 0 < n by trivial.
lemma k_pos : 0 < k by trivial.
lemma q_pos : 0 < q by trivial.

(* ==========================================================================
   SECTION 2: MODULAR ARITHMETIC
   ========================================================================== *)

op mod_q (x : int) : int = x %% q.

lemma mod_q_range x : 0 <= mod_q x < q.
proof. smt(). qed.

lemma mod_q_add a b : mod_q (a + b) = mod_q (mod_q a + mod_q b).
proof. smt(). qed.

lemma mod_q_self a : 0 <= a < q => mod_q a = a.
proof. smt(). qed.

(* ==========================================================================
   SECTION 3: VECTORS AS LISTS

   We represent vectors as int lists with implicit mod q arithmetic.
   ========================================================================== *)

type vec = int list.

(* map2: apply function pairwise to two lists *)
op map2 ['a 'b 'c] (f : 'a -> 'b -> 'c) (xs : 'a list) (ys : 'b list) : 'c list =
  with xs = [] => []
  with xs = x :: xs' =>
    if ys = [] then [] else f x (head witness ys) :: map2 f xs' (behead ys).

(* Component-wise operations *)
op vadd (a b : vec) : vec = map2 (fun x y => mod_q (x + y)) a b.
op vsub (a b : vec) : vec = map2 (fun x y => mod_q (x - y + q)) a b.
op vneg (a : vec) : vec = map (fun x => mod_q (q - x)) a.

op zero_vec (n : int) : vec = nseq n 0.

(* Valid vector: correct size, elements in range *)
op valid_vec (v : vec) (sz : int) : bool =
  size v = sz /\ all (fun x => 0 <= x < q) v.

(* ==========================================================================
   SECTION 4: KEY ALGEBRAIC LEMMAS
   ========================================================================== *)

(* Helper lemmas for map2 - base cases *)
lemma map2_nil_l ['a 'b 'c] (f : 'a -> 'b -> 'c) (ys : 'b list) :
  map2 f [] ys = [].
proof. by rewrite /map2. qed.

lemma map2_cons ['a 'b 'c] (f : 'a -> 'b -> 'c) (x : 'a) (xs' : 'a list) (y : 'b) (ys' : 'b list) :
  map2 f (x :: xs') (y :: ys') = f x y :: map2 f xs' ys'.
proof. by rewrite /map2. qed.

lemma map2_cons_nil ['a 'b 'c] (f : 'a -> 'b -> 'c) (x : 'a) (xs' : 'a list) :
  map2 f (x :: xs') [] = [].
proof. by rewrite /map2. qed.

(* PROVED: map2 preserves size *)
lemma size_map2 ['a 'b 'c] (f : 'a -> 'b -> 'c) (xs : 'a list) (ys : 'b list) :
  size (map2 f xs ys) = min (size xs) (size ys).
proof.
  elim: xs ys => [ys | x xs' IH ys].
  - by rewrite map2_nil_l /= /#.
  - case: ys => [| y ys'].
    + by rewrite map2_cons_nil /= /#.
    + by rewrite map2_cons /= IH /#.
qed.

(* PROVED: nth of map2 *)
lemma nth_map2 ['a 'b 'c] (f : 'a -> 'b -> 'c) x0 y0 z0 xs ys i :
  size xs = size ys =>
  0 <= i < size xs =>
  nth z0 (map2 f xs ys) i = f (nth x0 xs i) (nth y0 ys i).
proof.
  elim: xs ys i => [ys i Hsz Hi | x xs' IH ys i Hsz Hi].
  - by smt().
  - case: ys Hsz => [| y ys'] Hsz.
    + by smt().
    + rewrite map2_cons.
      case (i = 0) => [-> /= | Hne].
      * by trivial.
      * have Hi': 0 <= i - 1 < size xs' by smt().
        have Hsz': size xs' = size ys' by smt().
        smt().
qed.

(* Helper: elements of a valid vector are in range *)
lemma valid_vec_nth (v : vec) (sz : int) (i : int) :
  valid_vec v sz => 0 <= i < sz => 0 <= nth 0 v i < q.
proof.
  rewrite /valid_vec => [[Hsz Hall]] Hi.
  have Hmem : nth 0 v i \in v by smt(mem_nth).
  move: Hall; rewrite allP => /(_ (nth 0 v i) Hmem).
  done.
qed.

(* KEY arithmetic lemma: (a + b) mod q - b + q mod q = a when a,b in range *)
lemma mod_add_sub_cancel (a b : int) :
  0 <= a < q => 0 <= b < q =>
  mod_q (mod_q (a + b) - b + q) = a.
proof. smt(). qed.

(* KEY arithmetic lemma: (a - b + q) mod q + b mod q = a when a,b in range *)
lemma mod_sub_add_cancel (a b : int) :
  0 <= a < q => 0 <= b < q =>
  mod_q (mod_q (a - b + q) + b) = a.
proof. smt(). qed.

(* ==========================================================================
   THE KEY VECTOR ALGEBRA THEOREMS

   These are PROVED lemmas (not axioms). The proofs follow from:
   1. `eq_from_nth`: Two lists are equal iff same size and same elements
   2. `nth_map2`: Element access of map2 is pointwise function application
   3. `mod_add_sub_cancel`: (a+b) mod q - b + q mod q = a for a,b in [0,q)
   4. `mod_sub_add_cancel`: (a-b+q) mod q + b mod q = a for a,b in [0,q)

   The proofs are component-wise: for each index i, the arithmetic identity holds.
   ========================================================================== *)

(* ========== THE KEY THEOREM: (a + b) - b = a ========== *)
lemma vadd_vsub_cancel (a b : vec) :
  size a = size b =>
  valid_vec a (size a) =>
  valid_vec b (size b) =>
  vsub (vadd a b) b = a.
proof.
  move=> Hsz Hva Hvb.
  rewrite /vsub /vadd.
  apply (eq_from_nth 0).
  - (* Size preservation *)
    have H1 : size (map2 (fun x y => mod_q (x + y)) a b) = min (size a) (size b).
      exact: size_map2.
    have H2 : size (map2 (fun x y => mod_q (x - y + q))
                         (map2 (fun x y => mod_q (x + y)) a b) b)
              = min (size (map2 (fun x y => mod_q (x + y)) a b)) (size b).
      exact: size_map2.
    smt().
  - (* Element-wise equality *)
    move=> i Hi.
    have Hsize_inner : size (map2 (fun x y => mod_q (x + y)) a b) = min (size a) (size b)
      by exact: size_map2.
    have Hi_a : 0 <= i < size a by smt().
    have Hi_b : 0 <= i < size b by smt().
    have Ha_i := valid_vec_nth a (size a) i Hva Hi_a.
    have Hb_i := valid_vec_nth b (size b) i Hvb Hi_b.
    (* The key step: show nth of nested map2 equals original *)
    have Houter : nth 0 (map2 (fun x y => mod_q (x - y + q))
                              (map2 (fun x y => mod_q (x + y)) a b) b) i
                  = mod_q (nth 0 (map2 (fun x y => mod_q (x + y)) a b) i - nth 0 b i + q).
      rewrite (nth_map2 (fun x y => mod_q (x - y + q)) 0 0 0); first 2 smt().
      done.
    have Hinner : nth 0 (map2 (fun x y => mod_q (x + y)) a b) i
                  = mod_q (nth 0 a i + nth 0 b i).
      rewrite (nth_map2 (fun x y => mod_q (x + y)) 0 0 0); first 2 smt().
      done.
    rewrite Houter Hinner.
    exact: mod_add_sub_cancel.
qed.

(* ========== THE KEY THEOREM: (a - b) + b = a ========== *)
lemma vsub_vadd_cancel (a b : vec) :
  size a = size b =>
  valid_vec a (size a) =>
  valid_vec b (size b) =>
  vadd (vsub a b) b = a.
proof.
  move=> Hsz Hva Hvb.
  rewrite /vadd /vsub.
  apply (eq_from_nth 0).
  - (* Size preservation *)
    have H1 : size (map2 (fun x y => mod_q (x - y + q)) a b) = min (size a) (size b).
      exact: size_map2.
    have H2 : size (map2 (fun x y => mod_q (x + y))
                         (map2 (fun x y => mod_q (x - y + q)) a b) b)
              = min (size (map2 (fun x y => mod_q (x - y + q)) a b)) (size b).
      exact: size_map2.
    smt().
  - (* Element-wise equality *)
    move=> i Hi.
    have Hsize_inner : size (map2 (fun x y => mod_q (x - y + q)) a b) = min (size a) (size b)
      by exact: size_map2.
    have Hi_a : 0 <= i < size a by smt().
    have Hi_b : 0 <= i < size b by smt().
    have Ha_i := valid_vec_nth a (size a) i Hva Hi_a.
    have Hb_i := valid_vec_nth b (size b) i Hvb Hi_b.
    (* The key step: show nth of nested map2 equals original *)
    have Houter : nth 0 (map2 (fun x y => mod_q (x + y))
                              (map2 (fun x y => mod_q (x - y + q)) a b) b) i
                  = mod_q (nth 0 (map2 (fun x y => mod_q (x - y + q)) a b) i + nth 0 b i).
      rewrite (nth_map2 (fun x y => mod_q (x + y)) 0 0 0); first 2 smt().
      done.
    have Hinner : nth 0 (map2 (fun x y => mod_q (x - y + q)) a b) i
                  = mod_q (nth 0 a i - nth 0 b i + q).
      rewrite (nth_map2 (fun x y => mod_q (x - y + q)) 0 0 0); first 2 smt().
      done.
    rewrite Houter Hinner.
    exact: mod_sub_add_cancel.
qed.

(* ==========================================================================
   SECTION 5: ZERO POSITION MASKING
   ========================================================================== *)

type zpos = int list.  (* Indices to zero out *)

(* Apply zeros: set positions in P to 0 *)
op apply_zeros_v (v : vec) (P : zpos) : vec =
  mapi (fun i x => if i \in P then 0 else x) v.

(* Mask at zeros: keep only positions in P *)
op mask_zeros (v : vec) (P : zpos) : vec =
  mapi (fun i x => if i \in P then x else 0) v.

(* Mask at nonzeros: keep only positions NOT in P *)
op mask_nonzeros (v : vec) (P : zpos) : vec =
  mapi (fun i x => if i \in P then 0 else x) v.

(* KEY: apply_zeros = mask_nonzeros *)
lemma apply_zeros_eq_mask_nonzeros (v : vec) (P : zpos) :
  apply_zeros_v v P = mask_nonzeros v P.
proof. by rewrite /apply_zeros_v /mask_nonzeros. qed.

(* Concrete nth_mapi for vec type - use library lemma *)
(* EasyCrypt List library provides: nth_mapi *)
lemma nth_mapi_vec (f : int -> int -> int) (v : vec) (i : int) :
  0 <= i < size v =>
  nth 0 (mapi f v) i = f i (nth 0 v i).
proof.
  move=> Hi.
  by rewrite (nth_mapi 0) //; smt().
qed.

(* KEY: v = mask_zeros v P + mask_nonzeros v P *)
lemma vec_decomp (v : vec) (P : zpos) :
  valid_vec v (size v) =>
  v = vadd (mask_zeros v P) (mask_nonzeros v P).
proof.
  move=> [_ Hv].
  rewrite /vadd /mask_zeros /mask_nonzeros.
  apply (eq_from_nth 0).
  - have H1 : size (mapi (fun i x => if i \in P then x else 0) v) = size v by rewrite size_mapi.
    have H2 : size (mapi (fun i x => if i \in P then 0 else x) v) = size v by rewrite size_mapi.
    smt(size_map2).
  move=> i Hi.
  have Hsize1 : size (mapi (fun i x => if i \in P then x else 0) v) = size v by rewrite size_mapi.
  have Hsize2 : size (mapi (fun i x => if i \in P then 0 else x) v) = size v by rewrite size_mapi.
  have Hi' : 0 <= i < size v by smt(size_map2).
  have Hmask1 := nth_mapi_vec (fun i x => if i \in P then x else 0) v i Hi'.
  have Hmask2 := nth_mapi_vec (fun i x => if i \in P then 0 else x) v i Hi'.
  have Hrhs : nth 0 (map2 (fun x y => mod_q (x + y))
                          (mapi (fun i x => if i \in P then x else 0) v)
                          (mapi (fun i x => if i \in P then 0 else x) v)) i
            = mod_q (nth 0 (mapi (fun i x => if i \in P then x else 0) v) i +
                     nth 0 (mapi (fun i x => if i \in P then 0 else x) v) i).
    rewrite (nth_map2 (fun x y => mod_q (x + y)) 0 0 0); first 2 smt().
    done.
  rewrite Hrhs Hmask1 Hmask2.
  have Hv_i : 0 <= nth 0 v i < q.
    have Hmem : nth 0 v i \in v by smt(mem_nth).
    move: Hv; rewrite allP => /(_ (nth 0 v i) Hmem).
    done.
  case: (i \in P) => _ /=; smt().
qed.

(* KEY: apply_zeros is idempotent on mask_nonzeros *)
lemma apply_zeros_mask_nonzeros (v : vec) (P : zpos) :
  apply_zeros_v (mask_nonzeros v P) P = mask_nonzeros v P.
proof.
  rewrite /apply_zeros_v /mask_nonzeros.
  apply (eq_from_nth 0).
  - by rewrite !size_mapi.
  move=> i Hi.
  have Hsize : size (mapi (fun i x => if i \in P then 0 else x) v) = size v by rewrite size_mapi.
  have Hi' : 0 <= i < size v by smt().
  have Houter := nth_mapi_vec (fun i x => if i \in P then 0 else x)
                              (mapi (fun i x => if i \in P then 0 else x) v) i _.
  - by smt().
  have Hinner := nth_mapi_vec (fun i x => if i \in P then 0 else x) v i Hi'.
  rewrite Houter Hinner.
  (* Goal: (if i \in P then 0 else (if i \in P then 0 else nth 0 v i))
          = (if i \in P then 0 else nth 0 v i) *)
  smt().
qed.

(* KEY: apply_zeros annihilates mask_zeros (mask_zeros_complement) *)
lemma apply_zeros_mask_zeros (v : vec) (P : zpos) :
  apply_zeros_v (mask_zeros v P) P = zero_vec (size v).
proof.
  rewrite /apply_zeros_v /mask_zeros /zero_vec.
  apply (eq_from_nth 0).
  - by rewrite size_mapi size_nseq /#.
  move=> i Hi.
  have Hsize : size (mapi (fun i x => if i \in P then x else 0) v) = size v by rewrite size_mapi.
  have Hi' : 0 <= i < size v by smt().
  have Houter := nth_mapi_vec (fun i x => if i \in P then 0 else x)
                              (mapi (fun i x => if i \in P then x else 0) v) i _.
  - by smt().
  have Hinner := nth_mapi_vec (fun i x => if i \in P then x else 0) v i Hi'.
  rewrite Houter Hinner.
  (* Goal: (if i \in P then 0 else (if i \in P then nth 0 v i else 0)) = nth 0 (nseq (size v) 0) i *)
  have Hnseq : nth 0 (nseq (size v) 0) i = 0 by smt(nth_nseq).
  rewrite Hnseq.
  smt().
qed.

(* KEY: apply_zeros distributes over addition *)
lemma apply_zeros_linear (a b : vec) (P : zpos) :
  size a = size b =>
  apply_zeros_v (vadd a b) P = vadd (apply_zeros_v a P) (apply_zeros_v b P).
proof.
  move=> Hsz.
  rewrite /apply_zeros_v /vadd.
  apply (eq_from_nth 0).
  - (* Size proof *)
    have Hs1 : size (map2 (fun x y => mod_q (x + y)) a b) = min (size a) (size b)
      by exact: size_map2.
    have Hs2 : size (mapi (fun i x => if i \in P then 0 else x) a) = size a
      by rewrite size_mapi.
    have Hs3 : size (mapi (fun i x => if i \in P then 0 else x) b) = size b
      by rewrite size_mapi.
    have Hs4 : size (map2 (fun x y => mod_q (x + y))
                          (mapi (fun i x => if i \in P then 0 else x) a)
                          (mapi (fun i x => if i \in P then 0 else x) b))
              = min (size (mapi (fun i x => if i \in P then 0 else x) a))
                    (size (mapi (fun i x => if i \in P then 0 else x) b))
      by exact: size_map2.
    smt(size_mapi).
  move=> i Hi.
  have Hsize_inner : size (map2 (fun x y => mod_q (x + y)) a b) = min (size a) (size b)
    by exact: size_map2.
  have Hi_ab : 0 <= i < size a by smt().
  have Hi_inner : 0 <= i < size (map2 (fun x y => mod_q (x + y)) a b) by smt().
  (* LHS: nth of mapi applied to map2(a,b) *)
  have Hlhs := nth_mapi_vec (fun i x => if i \in P then 0 else x)
                            (map2 (fun x y => mod_q (x + y)) a b) i Hi_inner.
  have Hinner := nth_map2 (fun x y => mod_q (x + y)) 0 0 0 a b i _ _; first 2 smt().
  (* RHS: nth of map2 of two mapi results *)
  have Hsize_mapi_a : size (mapi (fun i x => if i \in P then 0 else x) a) = size a
    by rewrite size_mapi.
  have Hsize_mapi_b : size (mapi (fun i x => if i \in P then 0 else x) b) = size b
    by rewrite size_mapi.
  have Hrhs := nth_map2 (fun x y => mod_q (x + y)) 0 0 0
                        (mapi (fun i x => if i \in P then 0 else x) a)
                        (mapi (fun i x => if i \in P then 0 else x) b) i _ _.
  - smt(size_mapi).
  - smt(size_mapi).
  have Hmapi_a := nth_mapi_vec (fun i x => if i \in P then 0 else x) a i Hi_ab.
  have Hmapi_b := nth_mapi_vec (fun i x => if i \in P then 0 else x) b i _; first smt().
  rewrite Hlhs Hinner Hrhs Hmapi_a Hmapi_b.
  smt().
qed.

(* ==========================================================================
   SECTION 6: ADDITIONAL VECTOR ALGEBRA PROOFS
   ========================================================================== *)

(* KEY: a - b = a + (-b) *)
lemma vsub_is_vadd_vneg (a b : vec) :
  size a = size b =>
  vsub a b = vadd a (vneg b).
proof.
  move=> Hsz.
  rewrite /vsub /vadd /vneg.
  apply (eq_from_nth 0).
  - (* Size *)
    have Hs1 : size (map2 (fun x y => mod_q (x - y + q)) a b) = min (size a) (size b)
      by exact: size_map2.
    have Hs2 : size (map (fun x => mod_q (q - x)) b) = size b
      by rewrite size_map.
    have Hs3 : size (map2 (fun x y => mod_q (x + y)) a (map (fun x => mod_q (q - x)) b))
              = min (size a) (size (map (fun x => mod_q (q - x)) b))
      by exact: size_map2.
    smt(size_map).
  move=> i Hi.
  have Hsize1 : size (map2 (fun x y => mod_q (x - y + q)) a b) = min (size a) (size b)
    by exact: size_map2.
  have Hi_a : 0 <= i < size a by smt().
  have Hi_b : 0 <= i < size b by smt().
  have Hlhs := nth_map2 (fun x y => mod_q (x - y + q)) 0 0 0 a b i _ _; first 2 smt().
  have Hsize_neg : size (map (fun x => mod_q (q - x)) b) = size b by rewrite size_map.
  have Hrhs := nth_map2 (fun x y => mod_q (x + y)) 0 0 0 a
                        (map (fun x => mod_q (q - x)) b) i _ _; first 2 smt(size_map).
  have Hneg : nth 0 (map (fun x => mod_q (q - x)) b) i = mod_q (q - nth 0 b i).
    rewrite (nth_map 0 0) //; smt().
  rewrite Hlhs Hrhs Hneg.
  (* Goal: mod_q (a_i - b_i + q) = mod_q (a_i + mod_q (q - b_i)) *)
  smt().
qed.

(* KEY: -(-v) = v *)
lemma vneg_vneg (v : vec) :
  valid_vec v (size v) =>
  vneg (vneg v) = v.
proof.
  move=> [_ Hv].
  rewrite /vneg.
  apply (eq_from_nth 0).
  - by rewrite !size_map.
  move=> i Hi.
  have Hsize : size (map (fun x => mod_q (q - x)) v) = size v by rewrite size_map.
  have Hi' : 0 <= i < size v by smt(size_map).
  have Houter : nth 0 (map (fun x => mod_q (q - x)) (map (fun x => mod_q (q - x)) v)) i
              = mod_q (q - nth 0 (map (fun x => mod_q (q - x)) v) i).
    rewrite (nth_map 0 0) //; smt(size_map).
  have Hinner : nth 0 (map (fun x => mod_q (q - x)) v) i = mod_q (q - nth 0 v i).
    rewrite (nth_map 0 0) //; smt().
  rewrite Houter Hinner.
  (* Goal: mod_q (q - mod_q (q - v_i)) = v_i *)
  have Hv_i : 0 <= nth 0 v i < q.
    have Hmem : nth 0 v i \in v by smt(mem_nth).
    move: Hv; rewrite allP => /(_ (nth 0 v i) Hmem).
    done.
  smt().
qed.

(* KEY: v + 0 = v *)
lemma vadd_zero_vec (v : vec) (sz : int) :
  valid_vec v sz =>
  vadd v (zero_vec sz) = v.
proof.
  move=> [Hsz Hv].
  rewrite /vadd /zero_vec.
  apply (eq_from_nth 0).
  - have Hs1 : size (map2 (fun x y => mod_q (x + y)) v (nseq sz 0)) = min (size v) (size (nseq sz 0))
      by exact: size_map2.
    smt(size_nseq).
  move=> i Hi.
  have Hsize_nseq : size (nseq sz 0) = max 0 sz by rewrite size_nseq.
  have Hi_v : 0 <= i < size v by smt(size_map2 size_nseq).
  have Hrhs := nth_map2 (fun x y => mod_q (x + y)) 0 0 0 v (nseq sz 0) i _ _.
  - smt(size_nseq).
  - smt(size_nseq).
  have Hnseq : nth 0 (nseq sz 0) i = 0 by smt(nth_nseq).
  rewrite Hrhs Hnseq.
  have Hv_i : 0 <= nth 0 v i < q.
    have Hmem : nth 0 v i \in v by smt(mem_nth).
    move: Hv; rewrite allP => /(_ (nth 0 v i) Hmem).
    done.
  smt().
qed.

(* ==========================================================================
   SECTION 7: SUMMARY

   PROVED (machine-checked, no admits):
   1. vadd_vsub_cancel: (a + b) - b = a
   2. vsub_vadd_cancel: (a - b) + b = a
   3. vec_decomp: v = mask_zeros v P + mask_nonzeros v P
   4. apply_zeros_mask_nonzeros: apply_zeros(mask_nonzeros v P, P) = mask_nonzeros v P
   5. apply_zeros_linear: apply_zeros(a + b, P) = apply_zeros(a, P) + apply_zeros(b, P)
   6. vsub_is_vadd_vneg: a - b = a + (-b)
   7. vneg_vneg: -(-v) = v
   8. vadd_zero_vec: v + 0 = v

   These are the foundational lemmas for the simulation proof.
   ========================================================================== *)
