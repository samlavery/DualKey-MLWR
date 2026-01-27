(* ============================================================================
   Concrete Algebra Instantiation for Dual Public Key Signature Scheme

   This file provides concrete definitions for vector/matrix operations
   and PROVES the algebra axioms as lemmas, eliminating the need for axioms.

   STATUS: Template with admits - proofs can be filled in incrementally.
   All lemmas have correct signatures matching the axioms in Base.ec/LinearAlgebra.ec.

   IMPACT: Eliminates 9 vector algebra axioms + 4 mask axioms from Base.ec
   ============================================================================ *)

require import AllCore Distr List IntDiv Real.
require import StdOrder StdBigop.
import RealOrder IntOrder.

(* ==========================================================================
   SECTION 1: PARAMETERS (from Base.ec)
   ========================================================================== *)

op n : int = 128.        (* Ring dimension *)
op k : int = 4.          (* Module rank *)
op q : int = 4099.       (* Modulus *)
op vec_len : int = n * k.  (* Total vector length = 512 *)

lemma n_pos : 0 < n. proof. by rewrite /n. qed.
lemma k_pos : 0 < k. proof. by rewrite /k. qed.
lemma q_pos : 0 < q. proof. by rewrite /q. qed.
lemma vec_len_pos : 0 < vec_len. proof. by rewrite /vec_len /n /k. qed.

(* ==========================================================================
   SECTION 2: CONCRETE VECTOR TYPE

   Vectors are lists of integers of length vec_len, with arithmetic mod q.
   ========================================================================== *)

(* Modular reduction - standard positive representative *)
op mod_q (x : int) : int = x %% q.

(* Centered modular reduction - centered at 0 *)
op mod_center (x : int) : int =
  let r = x %% q in
  if q %/ 2 < r then r - q else r.

(* Concrete vector type: lists of integers *)
type Rq_vec_concrete = int list.

(* Well-formed vector predicate *)
op wf_vec (v : Rq_vec_concrete) : bool = size v = vec_len.

(* Zero vector *)
op zero_vec_c : Rq_vec_concrete = nseq vec_len 0.

lemma zero_vec_wf : wf_vec zero_vec_c.
proof. by rewrite /wf_vec /zero_vec_c size_nseq /vec_len /n /k; smt(). qed.

(* Pointwise vector addition *)
op vec_add_c (a b : Rq_vec_concrete) : Rq_vec_concrete =
  map (fun (p : int * int) => mod_center (fst p + snd p)) (zip a b).

(* Pointwise vector negation *)
op vec_neg_c (v : Rq_vec_concrete) : Rq_vec_concrete =
  map (fun x => mod_center (-x)) v.

(* Pointwise vector subtraction *)
op vec_sub_c (a b : Rq_vec_concrete) : Rq_vec_concrete =
  vec_add_c a (vec_neg_c b).

(* ==========================================================================
   SECTION 3: BASIC MODULAR ARITHMETIC LEMMAS
   ========================================================================== *)

lemma mod_center_0 : mod_center 0 = 0.
proof.
  rewrite /mod_center /=.
  have -> : 0 %% q = 0 by smt(q_pos).
  smt(q_pos).
qed.

lemma mod_center_add_comm (x y : int) :
  mod_center (x + y) = mod_center (y + x).
proof. by congr; ring. qed.

(* Value is in centered range [-q/2, q/2] *)
op in_centered_range (x : int) : bool = -(q %/ 2) <= x /\ x <= q %/ 2.

(* Double negation for centered values *)
lemma mod_center_neg_neg (x : int) :
  in_centered_range x => mod_center (- mod_center (- x)) = x.
proof.
  rewrite /in_centered_range /mod_center => [[Hlo Hhi]].
  have Hq2 : q %/ 2 = 2049 by rewrite /q.
  (* -x is in [-q/2, q/2], so -x %% q = -x + q if -x < 0, else -x *)
  smt(q_pos).
qed.

(* All elements of vector are in centered range *)
op reduced_vec (v : Rq_vec_concrete) : bool =
  all in_centered_range v.

(* Helper: reduced_vec implies nth is in centered range - PROVED *)
lemma reduced_vec_nth (v : Rq_vec_concrete) (i : int) :
  reduced_vec v => 0 <= i < size v => in_centered_range (nth witness v i).
proof.
  rewrite /reduced_vec => Hall Hi.
  by apply (allP in_centered_range v); [exact Hall | exact mem_nth].
qed.

(* ==========================================================================
   SECTION 4: VECTOR ALGEBRA LEMMAS (proving Base.ec axioms)
   ========================================================================== *)

(* Helper: zip preserves structure *)
lemma size_zip_eq (a b : 'a list) :
  size a = size b => size (zip a b) = size a.
proof. by move=> Heq; rewrite size_zip Heq minrE; smt(size_ge0). qed.

(* Helper lemma for nth of map with pairs - PROVED *)
lemma nth_map_zip_add (a b : int list) (i : int) :
  size a = size b => 0 <= i < size a =>
  nth witness (map (fun (p : int * int) => mod_center (fst p + snd p)) (zip a b)) i =
  mod_center (nth witness a i + nth witness b i).
proof.
  move=> Hsz Hi.
  rewrite (nth_map witness) 1:size_zip 1:/#.
  smt(nth_zip size_zip).
qed.

(* AXIOM 1: Commutativity of vector addition *)
lemma vec_add_comm_c (a b : Rq_vec_concrete) :
  wf_vec a => wf_vec b =>
  vec_add_c a b = vec_add_c b a.
proof.
  move=> wf_a wf_b; rewrite /vec_add_c /wf_vec.
  apply (eq_from_nth witness); first by rewrite !size_map !size_zip wf_a wf_b minrE; smt(size_ge0).
  move=> i Hi; smt(nth_map_zip_add).
qed.

(* AXIOM 2: Subtraction is addition of negation - by definition *)
lemma vec_sub_is_add_neg_c (a b : Rq_vec_concrete) :
  vec_sub_c a b = vec_add_c a (vec_neg_c b).
proof. by rewrite /vec_sub_c. qed.

(* AXIOM 3: Negation is involutive (for reduced vectors) *)
lemma vec_neg_neg_c (v : Rq_vec_concrete) :
  wf_vec v => reduced_vec v => vec_neg_c (vec_neg_c v) = v.
proof.
  move=> wf_v red_v; rewrite /vec_neg_c.
  apply (eq_from_nth witness); first by rewrite !size_map.
  move=> i Hi.
  rewrite (nth_map witness) 1:/# (nth_map witness) 1:/#.
  have Hin := reduced_vec_nth v i red_v _.
    by smt(size_map).
  exact (mod_center_neg_neg _ Hin).
qed.

(* Helper: mod_center is identity on centered values - PROVED *)
lemma mod_center_id (x : int) :
  in_centered_range x => mod_center x = x.
proof.
  rewrite /in_centered_range /mod_center /q => [[Hlo Hhi]].
  case (0 <= x) => Hsgn.
  - have ->: x %% 4099 = x by smt().
    by smt().
  - have Hr: x %% 4099 = x + 4099 by smt().
    rewrite Hr; by smt().
qed.

(* Helper: mod_center of x+0 for centered x - PROVED *)
lemma mod_center_add_zero (x : int) :
  in_centered_range x => mod_center (x + 0) = x.
proof.
  move=> Hin.
  have ->: x + 0 = x by ring.
  by apply mod_center_id.
qed.

(* Helper: nth of vec_add_c - PROVED *)
lemma vec_add_c_nth (a b : int list) (i : int) :
  size a = size b => 0 <= i < size a =>
  nth witness (vec_add_c a b) i = mod_center (nth witness a i + nth witness b i).
proof.
  rewrite /vec_add_c => Hsz Hi.
  rewrite (nth_map witness) 1:size_zip 1:/#.
  smt(nth_zip).
qed.

(* Helper: vec_len evaluates to 512 *)
lemma vec_len_val : vec_len = 512.
proof. by rewrite /vec_len /n /k. qed.

(* AXIOM 4: Adding zero is identity (for reduced vectors) - PROVED *)
lemma vec_add_zero_r_c (v : Rq_vec_concrete) :
  wf_vec v => reduced_vec v => vec_add_c v zero_vec_c = v.
proof.
  rewrite /wf_vec /zero_vec_c vec_len_val => Hwf Hred.
  apply (eq_from_nth witness).
  - rewrite /vec_add_c size_map size_zip size_nseq /#.
  - move=> i Hi.
    have Hszn : size (nseq 512 0) = 512 by smt(size_nseq).
    have Hin : 0 <= i < size v by smt().
    rewrite vec_add_c_nth.
      by rewrite Hszn.
      by smt().
    rewrite nth_nseq 1:/#.
    have Hcent := reduced_vec_nth v i Hred Hin.
    have ->: nth witness v i + 0 = nth witness v i by ring.
    by apply mod_center_id.
qed.

(* Two values with same residue mod q have same mod_center *)
lemma mod_center_eq_from_residue (x y : int) :
  x %% q = y %% q => mod_center x = mod_center y.
proof.
  rewrite /mod_center => H.
  by rewrite H.
qed.

(* Key property: mod_center(x) is congruent to x mod q *)
lemma mod_center_congr (x : int) : mod_center x %% q = x %% q.
proof.
  rewrite /mod_center /=.
  case (q %/ 2 < x %% q) => H.
  - smt(q_pos).
  - smt(q_pos).
qed.

(* Key property: x + mod_center(-x) ≡ 0 (mod q) *)
lemma add_neg_mod_center_congr (x : int) : (x + mod_center (-x)) %% q = 0.
proof.
  have H1 : mod_center (-x) %% q = (-x) %% q by apply mod_center_congr.
  smt(q_pos).
qed.

(* The main helper: mod_center(x + mod_center(-x)) = 0 *)
lemma mod_center_add_neg (x : int) : mod_center (x + mod_center (-x)) = 0.
proof.
  have H := add_neg_mod_center_congr x.
  rewrite /mod_center.
  have -> : (x + mod_center (-x)) %% q = 0 by exact H.
  by smt(q_pos).
qed.

(* Helper: size of vec_neg_c *)
lemma size_vec_neg_c (v : int list) : size (vec_neg_c v) = size v.
proof. by rewrite /vec_neg_c size_map. qed.

prover timeout=60.

(* AXIOM 6: Inverse - adding negation gives zero - PROVED *)
lemma vec_add_neg_cancel_c (v : Rq_vec_concrete) :
  wf_vec v => vec_add_c v (vec_neg_c v) = zero_vec_c.
proof.
  rewrite /wf_vec /zero_vec_c vec_len_val /vec_add_c /vec_neg_c => Hwf.
  apply (eq_from_nth witness).
  - rewrite size_map size_zip size_map size_nseq /#.
  - move=> i Hi.
    have Hin : 0 <= i < size v.
      rewrite size_map size_zip size_map in Hi.
      smt().
    rewrite (nth_map witness) 1:size_zip 1:size_map 1:/#.
    rewrite nth_nseq 1:/#.
    smt(nth_zip nth_map mod_center_add_neg size_map).
qed.

(* Key: (mod_center(a+b) + c) has same residue as (a + b + c) *)
lemma mc_add_residue (a b c : int) :
  (mod_center (a + b) + c) %% q = (a + b + c) %% q.
proof.
  have H : mod_center (a + b) %% q = (a + b) %% q by apply mod_center_congr.
  smt(q_pos).
qed.

(* Key: (a + mod_center(b+c)) has same residue as (a + b + c) *)
lemma mc_add_residue_r (a b c : int) :
  (a + mod_center (b + c)) %% q = (a + b + c) %% q.
proof.
  have H : mod_center (b + c) %% q = (b + c) %% q by apply mod_center_congr.
  smt(q_pos).
qed.

(* Both sides have same residue, so mod_center gives same result *)
lemma mod_center_assoc (a b c : int) :
  mod_center (mod_center (a + b) + c) = mod_center (a + mod_center (b + c)).
proof.
  apply mod_center_eq_from_residue.
  rewrite mc_add_residue mc_add_residue_r.
  done.
qed.

(* Helper: size of vec_add_c *)
lemma size_vec_add_c (a b : int list) :
  size a = size b => size (vec_add_c a b) = size a.
proof.
  rewrite /vec_add_c => Hsz.
  by rewrite size_map size_zip /#.
qed.

(* AXIOM 5: Associativity of vector addition - PROVED *)
lemma vec_add_assoc_c (a b c : Rq_vec_concrete) :
  wf_vec a => wf_vec b => wf_vec c =>
  vec_add_c (vec_add_c a b) c = vec_add_c a (vec_add_c b c).
proof.
  rewrite /wf_vec => Ha Hb Hc.
  apply (eq_from_nth witness).
  - rewrite !size_vec_add_c /#.
  - move=> i Hi.
    have Hsab : size a = size b by smt().
    have Hsbc : size b = size c by smt().
    have Hin : 0 <= i < size a by smt(size_vec_add_c).
    smt(vec_add_c_nth size_vec_add_c mod_center_assoc).
qed.

(* ==========================================================================
   SECTION 5: MASK OPERATIONS (concrete)
   ========================================================================== *)

(* Zero position set - list of indices that should be zero *)
type zero_pos_concrete = int list.

(* Check if index is in zero positions *)
op is_zero_pos (P : zero_pos_concrete) (i : int) : bool = i \in P.

(* Apply zeros: set positions in P to zero *)
op apply_zeros_c (v : Rq_vec_concrete) (P : zero_pos_concrete) : Rq_vec_concrete =
  mapi (fun i x => if is_zero_pos P i then 0 else x) v.

(* Mask at zeros: keep only positions in P *)
op mask_at_zeros_c (v : Rq_vec_concrete) (P : zero_pos_concrete) : Rq_vec_concrete =
  mapi (fun i x => if is_zero_pos P i then x else 0) v.

(* Mask at nonzeros: keep only positions NOT in P *)
op mask_at_nonzeros_c (v : Rq_vec_concrete) (P : zero_pos_concrete) : Rq_vec_concrete =
  mapi (fun i x => if is_zero_pos P i then 0 else x) v.

(* ==========================================================================
   SECTION 6: MASK ALGEBRA LEMMAS (proving LinearAlgebra.ec axioms)
   ========================================================================== *)

(* LEMMA: Vector decomposition - by pointwise case analysis on is_zero_pos
   Note: Requires reduced_vec because mod_center is only identity on centered values *)
lemma vec_decomposition_c (v : Rq_vec_concrete) (P : zero_pos_concrete) :
  wf_vec v => reduced_vec v =>
  v = vec_add_c (mask_at_zeros_c v P) (mask_at_nonzeros_c v P).
proof.
  rewrite /wf_vec /vec_add_c /mask_at_zeros_c /mask_at_nonzeros_c => Hsz Hred.
  apply (eq_from_nth witness).
  - rewrite size_map size_zip !size_mapi /#.
  - move=> i Hi.
    have Hin : 0 <= i < size v by smt(size_map size_zip size_mapi).
    have Hcent : in_centered_range (nth witness v i) by apply reduced_vec_nth.
    (* RHS *)
    have RHS_eq : nth witness (map (fun (p : int * int) => mod_center (fst p + snd p))
                    (zip (mapi (fun j x => if is_zero_pos P j then x else 0) v)
                         (mapi (fun j x => if is_zero_pos P j then 0 else x) v))) i =
                  mod_center (fst (nth witness
                                (zip (mapi (fun j x => if is_zero_pos P j then x else 0) v)
                                     (mapi (fun j x => if is_zero_pos P j then 0 else x) v)) i) +
                              snd (nth witness
                                (zip (mapi (fun j x => if is_zero_pos P j then x else 0) v)
                                     (mapi (fun j x => if is_zero_pos P j then 0 else x) v)) i))
      by rewrite (nth_map witness) 1:size_zip 1:!size_mapi //#.
    have Eq_zip : nth witness (zip (mapi (fun j x => if is_zero_pos P j then x else 0) v)
                                   (mapi (fun j x => if is_zero_pos P j then 0 else x) v)) i =
                  (nth witness (mapi (fun j x => if is_zero_pos P j then x else 0) v) i,
                   nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x) v) i)
      by smt(nth_zip size_mapi).
    have Eq_z : nth witness (mapi (fun j x => if is_zero_pos P j then x else 0) v) i =
                (fun j x => if is_zero_pos P j then x else 0) i (nth witness v i)
      by apply nth_mapi.
    have Eq_nz : nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x) v) i =
                 (fun j x => if is_zero_pos P j then 0 else x) i (nth witness v i)
      by apply nth_mapi.
    rewrite RHS_eq Eq_zip /= Eq_z Eq_nz /=.
    case (is_zero_pos P i) => Hp /=.
    - (* At P position: v[i] + 0 = v[i] *)
      by smt(mod_center_id).
    - (* Not at P position: 0 + v[i] = v[i] *)
      by smt(mod_center_id).
qed.

(* Key observation: apply_zeros_c = mask_at_nonzeros_c *)
lemma apply_zeros_eq_mask_nonzeros (v : Rq_vec_concrete) (P : zero_pos_concrete) :
  apply_zeros_c v P = mask_at_nonzeros_c v P.
proof. by rewrite /apply_zeros_c /mask_at_nonzeros_c. qed.

(* AXIOM 7: mask_nonzeros_at_zeros - masking is idempotent - PROVED *)
lemma mask_nonzeros_at_zeros_c (v : Rq_vec_concrete) (P : zero_pos_concrete) :
  wf_vec v =>
  apply_zeros_c (mask_at_nonzeros_c v P) P = mask_at_nonzeros_c v P.
proof.
  move=> Hwf.
  rewrite apply_zeros_eq_mask_nonzeros /mask_at_nonzeros_c.
  apply (eq_from_nth witness).
  - by rewrite !size_mapi.
  - move=> i Hi.
    have Hin : 0 <= i < size v by smt(size_mapi).
    have Eq1 : nth witness (mapi (fun i x => if is_zero_pos P i then 0 else x)
                 (mapi (fun i x => if is_zero_pos P i then 0 else x) v)) i =
               (fun i x => if is_zero_pos P i then 0 else x) i
               (nth witness (mapi (fun i x => if is_zero_pos P i then 0 else x) v) i)
      by apply nth_mapi; smt(size_mapi).
    have Eq2 : nth witness (mapi (fun i x => if is_zero_pos P i then 0 else x) v) i =
               (fun i x => if is_zero_pos P i then 0 else x) i (nth witness v i)
      by apply nth_mapi.
    rewrite Eq1 Eq2 /=.
    case (is_zero_pos P i) => Hp; done.
qed.

(* LEMMA: mask_zeros_complement - at P positions, apply_zeros sets to 0; at non-P, mask_at_zeros already 0 *)
lemma mask_zeros_complement_c (v : Rq_vec_concrete) (P : zero_pos_concrete) :
  wf_vec v =>
  apply_zeros_c (mask_at_zeros_c v P) P = zero_vec_c.
proof.
  rewrite /wf_vec /apply_zeros_c /mask_at_zeros_c /zero_vec_c => Hwf.
  apply (eq_from_nth witness).
  - rewrite !size_mapi size_nseq /#.
  - move=> i Hi.
    have Hin : 0 <= i < size v by smt(size_mapi size_nseq).
    rewrite nth_nseq 1:/#.
    have Eq1 : nth witness (mapi (fun i x => if is_zero_pos P i then 0 else x)
                 (mapi (fun i x => if is_zero_pos P i then x else 0) v)) i =
               (fun i x => if is_zero_pos P i then 0 else x) i
               (nth witness (mapi (fun i x => if is_zero_pos P i then x else 0) v) i)
      by apply nth_mapi; smt(size_mapi).
    have Eq2 : nth witness (mapi (fun i x => if is_zero_pos P i then x else 0) v) i =
               (fun i x => if is_zero_pos P i then x else 0) i (nth witness v i)
      by apply nth_mapi.
    rewrite Eq1 Eq2 /=.
    case (is_zero_pos P i) => Hp; done.
qed.

(* LEMMA: apply_zeros is linear - distributes over addition *)
prover timeout=120.

lemma apply_zeros_linear_c (a b : Rq_vec_concrete) (P : zero_pos_concrete) :
  wf_vec a => wf_vec b =>
  apply_zeros_c (vec_add_c a b) P = vec_add_c (apply_zeros_c a P) (apply_zeros_c b P).
proof.
  rewrite /wf_vec /apply_zeros_c /vec_add_c => Ha Hb.
  have Hsab : size a = size b by smt().
  apply (eq_from_nth witness).
  - smt(size_mapi size_map size_zip).
  - move=> i Hi.
    have Hin_a : 0 <= i < size a by smt(size_mapi size_map size_zip).
    have Hin_b : 0 <= i < size b by smt().
    (* LHS *)
    have LHS_eq : nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x)
                    (map (fun (p : int * int) => mod_center (fst p + snd p)) (zip a b))) i =
                  (fun j x => if is_zero_pos P j then 0 else x) i
                  (nth witness (map (fun (p : int * int) => mod_center (fst p + snd p)) (zip a b)) i)
      by apply nth_mapi; smt(size_map size_zip).
    have LHS_inner : nth witness (map (fun (p : int * int) => mod_center (fst p + snd p)) (zip a b)) i =
                     mod_center (nth witness a i + nth witness b i)
      by rewrite (nth_map witness) 1:size_zip 1:/#; smt(nth_zip).
    (* RHS *)
    have RHS_eq : nth witness (map (fun (p : int * int) => mod_center (fst p + snd p))
                    (zip (mapi (fun j x => if is_zero_pos P j then 0 else x) a)
                         (mapi (fun j x => if is_zero_pos P j then 0 else x) b))) i =
                  mod_center (nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x) a) i +
                              nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x) b) i)
      by rewrite (nth_map witness) 1:size_zip 1:!size_mapi 1:/#; smt(nth_zip size_mapi).
    have RHS_a : nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x) a) i =
                 (fun j x => if is_zero_pos P j then 0 else x) i (nth witness a i)
      by apply nth_mapi.
    have RHS_b : nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x) b) i =
                 (fun j x => if is_zero_pos P j then 0 else x) i (nth witness b i)
      by apply nth_mapi.
    rewrite LHS_eq LHS_inner RHS_eq RHS_a RHS_b /=.
    case (is_zero_pos P i) => Hp.
    - by rewrite mod_center_0.
    - done.
qed.

(* LEMMA: apply_zeros preserves negation *)
lemma mod_center_neg_0 : mod_center (-0) = 0.
proof.
  rewrite /mod_center /=.
  have -> : (-0) %% q = 0 by smt(q_pos).
  smt(q_pos).
qed.

lemma apply_zeros_neg_c (v : Rq_vec_concrete) (P : zero_pos_concrete) :
  wf_vec v =>
  apply_zeros_c (vec_neg_c v) P = vec_neg_c (apply_zeros_c v P).
proof.
  rewrite /wf_vec /apply_zeros_c /vec_neg_c => Hwf.
  apply (eq_from_nth witness).
  - smt(size_mapi size_map).
  - move=> i Hi.
    have Hin : 0 <= i < size v by smt(size_mapi size_map).
    (* LHS: mapi ... (map neg v) *)
    have LHS_eq : nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x)
                    (map (fun x => mod_center (-x)) v)) i =
                  (fun j x => if is_zero_pos P j then 0 else x) i
                  (nth witness (map (fun x => mod_center (-x)) v) i)
      by apply nth_mapi; smt(size_map).
    have LHS_inner : nth witness (map (fun x => mod_center (-x)) v) i =
                     mod_center (- nth witness v i)
      by rewrite (nth_map witness) //#.
    (* RHS: map neg (mapi ... v) *)
    have RHS_eq : nth witness (map (fun x => mod_center (-x))
                    (mapi (fun j x => if is_zero_pos P j then 0 else x) v)) i =
                  mod_center (- nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x) v) i)
      by rewrite (nth_map witness) 1:size_mapi //#.
    have RHS_inner : nth witness (mapi (fun j x => if is_zero_pos P j then 0 else x) v) i =
                     (fun j x => if is_zero_pos P j then 0 else x) i (nth witness v i)
      by apply nth_mapi.
    rewrite LHS_eq LHS_inner RHS_eq RHS_inner /=.
    case (is_zero_pos P i) => Hp.
    - by rewrite mod_center_neg_0.
    - done.
qed.

(* ==========================================================================
   SECTION 7: MATRIX-VECTOR MULTIPLICATION
   ========================================================================== *)

(* Matrix type: list of row vectors *)
type Rq_mat_concrete = Rq_vec_concrete list.

(* Dot product of two vectors *)
op dot_product (a b : Rq_vec_concrete) : int =
  foldl (fun acc (p : int * int) => mod_center (acc + fst p * snd p)) 0 (zip a b).

(* Matrix-vector multiplication *)
op mat_vec_mul_c (M : Rq_mat_concrete) (v : Rq_vec_concrete) : Rq_vec_concrete =
  map (fun row => dot_product row v) M.

(* ---------- Helper lemmas for mat_vec_mul_neg_c proof ---------- *)

(* mod_center(x) is in range [-(q-1)/2, q/2] *)
lemma mod_center_range (x : int) :
  -(q %/ 2) <= mod_center x /\ mod_center x <= q %/ 2.
proof.
  rewrite /mod_center /=.
  have Hmod : 0 <= x %% q < q by smt(modz_ge0 ltz_pmod q_pos).
  case (q %/ 2 < x %% q) => H; smt().
qed.

(* Two centered values with same mod q are equal *)
lemma mod_center_unique (x y : int) :
  x %% q = y %% q =>
  -(q %/ 2) <= x /\ x <= q %/ 2 =>
  -(q %/ 2) <= y /\ y <= q %/ 2 =>
  x = y.
proof. smt(). qed.

(* Equality of mod_center values from mod q equality *)
lemma mod_center_eq_from_mod (x y : int) :
  mod_center x %% q = mod_center y %% q => mod_center x = mod_center y.
proof.
  move=> Heq.
  have Hx := mod_center_range x.
  have Hy := mod_center_range y.
  by apply mod_center_unique.
qed.

prover timeout=60.

(* Generalized dot product negation: inductive step *)
lemma dot_neg_step (acc : int) (a_i b_i : int) :
  mod_center (mod_center (-acc) + a_i * mod_center (-b_i)) %% q =
  mod_center (-(mod_center (acc + a_i * b_i))) %% q.
proof.
  have H1 : mod_center (mod_center (-acc) + a_i * mod_center (-b_i)) %% q =
            (mod_center (-acc) + a_i * mod_center (-b_i)) %% q
    by apply mod_center_congr.
  have H2 : mod_center (-(mod_center (acc + a_i * b_i))) %% q =
            (-(mod_center (acc + a_i * b_i))) %% q
    by apply mod_center_congr.
  have H3 : mod_center (-acc) %% q = (-acc) %% q by apply mod_center_congr.
  have H4 : mod_center (-b_i) %% q = (-b_i) %% q by apply mod_center_congr.
  have H5 : mod_center (acc + a_i * b_i) %% q = (acc + a_i * b_i) %% q
    by apply mod_center_congr.
  have Hprod : (a_i * mod_center (-b_i)) %% q = (a_i * (-b_i)) %% q
    by smt(modzMml modzMmr).
  have Hlhs : (mod_center (-acc) + a_i * mod_center (-b_i)) %% q = (-acc + a_i * (-b_i)) %% q
    by smt(modzDml modzDmr modzMml modzMmr).
  have Hrhs : (-(mod_center (acc + a_i * b_i))) %% q = (-(acc + a_i * b_i)) %% q
    by smt(modzNm).
  smt().
qed.

(* General dot_product_neg: works for any sizes because zip truncates *)
lemma dot_product_neg_gen (a b : int list) :
  dot_product a (map (fun x => mod_center (-x)) b) =
  mod_center (- dot_product a b).
proof.
  rewrite /dot_product.
  rewrite zip_mapr.
  have Hzip : forall l acc,
    foldl (fun a (p : int * int) => mod_center (a + fst p * snd p)) acc
          (map (fun (xy : int * int) => (xy.`1, mod_center (- xy.`2))) l) =
    foldl (fun a (p : int * int) => mod_center (a + fst p * mod_center (- snd p)))
          acc l.
    elim => [|p l IH] acc //=.
    by rewrite IH.
  rewrite Hzip.
  have Hrel : forall l acc,
    foldl (fun a (p : int * int) => mod_center (a + fst p * mod_center (- snd p)))
          (mod_center (-acc)) l =
    mod_center (- foldl (fun a (p : int * int) => mod_center (a + fst p * snd p)) acc l).
    elim => [|p l IH] acc //=.
    have Hstep : mod_center (mod_center (-acc) + p.`1 * mod_center (-p.`2)) =
                 mod_center (-(mod_center (acc + p.`1 * p.`2))).
      apply mod_center_eq_from_mod.
      apply dot_neg_step.
    by rewrite Hstep IH.
  have Hz : mod_center (-0) = 0 by smt(mod_center_range).
  rewrite -Hz.
  by apply Hrel.
qed.

(* ---------- Helper lemmas for mat_vec_mul_linear_c proof ---------- *)

prover timeout=180.

(* Key step lemma: accumulator step with added vector element equals adding individual products *)
lemma dot_add_step (acc1 acc2 : int) (r a b : int) :
  mod_center (mod_center (acc1 + acc2) + r * mod_center (a + b)) %% q =
  mod_center (mod_center (acc1 + r * a) + mod_center (acc2 + r * b)) %% q.
proof.
  have Hlhs : mod_center (mod_center (acc1 + acc2) + r * mod_center (a + b)) %% q =
              (acc1 + acc2 + r * (a + b)) %% q
    by smt(mod_center_congr modzDml modzDmr modzMml modzMmr).
  have Hrhs : mod_center (mod_center (acc1 + r * a) + mod_center (acc2 + r * b)) %% q =
              (acc1 + r * a + acc2 + r * b) %% q
    by smt(mod_center_congr modzDml modzDmr modzMml modzMmr).
  smt().
qed.

(* Core induction lemma over zip3 structure *)
lemma dot_add_foldl_zip3 (l : (int * (int * int)) list) (acc1 acc2 : int) :
  foldl (fun acc (p : int * (int * int)) => mod_center (acc + fst p * mod_center (fst (snd p) + snd (snd p))))
        (mod_center (acc1 + acc2)) l =
  mod_center (
    foldl (fun acc (p : int * (int * int)) => mod_center (acc + fst p * fst (snd p))) acc1 l +
    foldl (fun acc (p : int * (int * int)) => mod_center (acc + fst p * snd (snd p))) acc2 l).
proof.
  elim: l acc1 acc2 => [|p l IH] acc1 acc2 /=; first done.
  have Hacc : mod_center (mod_center (acc1 + acc2) + p.`1 * mod_center (p.`2.`1 + p.`2.`2)) =
              mod_center (mod_center (acc1 + p.`1 * p.`2.`1) + mod_center (acc2 + p.`1 * p.`2.`2)).
    apply mod_center_eq_from_mod.
    apply dot_add_step.
  rewrite Hacc.
  by apply (IH (mod_center (acc1 + p.`1 * p.`2.`1)) (mod_center (acc2 + p.`1 * p.`2.`2))).
qed.

(* Transform foldl on zip with mapped list to foldl on zip3 *)
lemma foldl_zip_map_to_zip3 (row a b : int list) (acc : int) :
  foldl (fun acc (p : int * int) => mod_center (acc + fst p * snd p)) acc
        (zip row (map (fun (p : int * int) => mod_center (fst p + snd p)) (zip a b))) =
  foldl (fun acc (p : int * (int * int)) => mod_center (acc + fst p * mod_center (fst (snd p) + snd (snd p)))) acc
        (zip row (zip a b)).
proof.
  rewrite zip_mapr.
  have Heq : forall l acc,
    foldl (fun a0 (p : int * int) => mod_center (a0 + fst p * snd p)) acc
          (map (fun (xy : int * (int * int)) => (xy.`1, mod_center (xy.`2.`1 + xy.`2.`2))) l) =
    foldl (fun a0 (p : int * (int * int)) => mod_center (a0 + fst p * mod_center (fst (snd p) + snd (snd p)))) acc l.
    elim => [|p l IH] acc0 //=.
    by rewrite IH.
  by apply Heq.
qed.

(* Helper: foldl on zip3 projecting left equals foldl on zip with left list *)
lemma foldl_zip3_left_aux (l1 l2 l3 : int list) (acc : int) :
  size l2 = size l3 =>
  foldl (fun a0 (p : int * int) => mod_center (a0 + fst p * snd p)) acc (zip l1 l2) =
  foldl (fun a0 (p : int * (int * int)) => mod_center (a0 + fst p * fst (snd p))) acc (zip l1 (zip l2 l3)).
proof.
  elim: l1 l2 l3 acc => [|x l1 IH] l2 l3 acc Hsz; first by rewrite !zip0l.
  case: l2 Hsz => [|y2 l2] Hsz; first smt(size_ge0).
  case: l3 Hsz => [|y3 l3] Hsz /=; first smt(size_ge0).
  have Hsz' : size l2 = size l3 by smt().
  by apply (IH l2 l3 (mod_center (acc + x * y2)) Hsz').
qed.

(* Helper: foldl on zip3 projecting right equals foldl on zip with right list *)
lemma foldl_zip3_right_aux (l1 l2 l3 : int list) (acc : int) :
  size l2 = size l3 =>
  foldl (fun a0 (p : int * int) => mod_center (a0 + fst p * snd p)) acc (zip l1 l3) =
  foldl (fun a0 (p : int * (int * int)) => mod_center (a0 + fst p * snd (snd p))) acc (zip l1 (zip l2 l3)).
proof.
  elim: l1 l2 l3 acc => [|x l1 IH] l2 l3 acc Hsz; first by rewrite !zip0l.
  case: l2 Hsz => [|y2 l2] Hsz; first smt(size_ge0).
  case: l3 Hsz => [|y3 l3] Hsz /=; first smt(size_ge0).
  have Hsz' : size l2 = size l3 by smt().
  by apply (IH l2 l3 (mod_center (acc + x * y3)) Hsz').
qed.

(* Main lemma: dot_product distributes over vec_add_c *)
lemma dot_product_add_gen (row a b : int list) :
  size a = size b =>
  dot_product row (vec_add_c a b) = mod_center (dot_product row a + dot_product row b).
proof.
  move=> Hsz.
  rewrite /dot_product /vec_add_c.
  rewrite foldl_zip_map_to_zip3.
  have Hz : mod_center (0 + 0) = 0 by smt(mod_center_range).
  rewrite -Hz.
  rewrite dot_add_foldl_zip3.
  congr.
  - by rewrite (foldl_zip3_left_aux row a b 0 Hsz).
  - by rewrite (foldl_zip3_right_aux row a b 0 Hsz).
qed.

(* Helper: zip_map distributes *)
lemma zip_map_map_int (f : int -> int) (g : int -> int) (l1 : int list) (l2 : int list) :
  zip (map f l1) (map g l2) = map (fun (p : int * int) => (f (fst p), g (snd p))) (zip l1 l2).
proof.
  elim: l1 l2 => [|x l1 IH] l2 //=.
  case: l2 => //= y l2.
  by rewrite IH.
qed.

(* ---------- End helper lemmas ---------- *)

(* LEMMA: mat_vec_mul is linear - dot_product distributes over vector addition *)
lemma mat_vec_mul_linear_c (M : Rq_mat_concrete) (a b : Rq_vec_concrete) :
  wf_vec a => wf_vec b =>
  mat_vec_mul_c M (vec_add_c a b) = vec_add_c (mat_vec_mul_c M a) (mat_vec_mul_c M b).
proof.
  rewrite /wf_vec => Hsza Hszb.
  have Hszeq : size a = size b by smt().
  rewrite /mat_vec_mul_c /vec_add_c.
  rewrite zip_map_map_int.
  rewrite -map_comp.
  apply eq_map => row.
  rewrite /(\o) /=.
  by apply dot_product_add_gen.
qed.

(* LEMMA: mat_vec_mul preserves negation - dot_product preserves negation *)
lemma mat_vec_mul_neg_c (M : Rq_mat_concrete) (v : Rq_vec_concrete) :
  wf_vec v =>
  mat_vec_mul_c M (vec_neg_c v) = vec_neg_c (mat_vec_mul_c M v).
proof.
  rewrite /wf_vec => Hsz.
  rewrite /mat_vec_mul_c /vec_neg_c.
  rewrite -map_comp.
  apply eq_map => row.
  by apply dot_product_neg_gen.
qed.

(* ==========================================================================
   SECTION 8: SUMMARY OF AXIOMS ELIMINATED

   ALL 13 AXIOMS HAVE BEEN CONVERTED TO LEMMAS!

   FROM Base.ec (9 axioms -> all proven):
   1. vec_add_comm       -> vec_add_comm_c       [PROVEN]
   2. vec_sub_is_add_neg -> vec_sub_is_add_neg_c [PROVEN by definition]
   3. vec_neg_neg        -> vec_neg_neg_c        [PROVEN]
   4. vec_add_zero_r     -> vec_add_zero_r_c     [PROVEN]
   5. vec_add_assoc      -> vec_add_assoc_c      [PROVEN]
   6. vec_add_neg_cancel -> vec_add_neg_cancel_c [PROVEN]
   7. mat_vec_mul_linear -> mat_vec_mul_linear_c [PROVEN]
   8. mat_vec_mul_neg    -> mat_vec_mul_neg_c    [PROVEN]
   9. apply_zeros_neg    -> apply_zeros_neg_c    [PROVEN]

   FROM LinearAlgebra.ec (4 axioms -> all proven):
   1. vec_decomposition     -> vec_decomposition_c     [PROVEN]
   2. mask_nonzeros_at_zeros -> mask_nonzeros_at_zeros_c [PROVEN]
   3. mask_zeros_complement  -> mask_zeros_complement_c  [PROVEN]
   4. apply_zeros_linear     -> apply_zeros_linear_c     [PROVEN]

   TOTAL: 13/13 axioms converted to lemmas = 0 remaining axioms!
   ========================================================================== *)

