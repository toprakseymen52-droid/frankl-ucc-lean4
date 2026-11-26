/-!
# Formal Proof of Christopher Bouchard's Open Question 2.2 (arXiv:2310.02482v2)

Zero external dependencies (pure Lean 4 core). Zero `sorry`, zero custom axioms.

Main results:
1. `intersection_witness_lemma`: If `C` is a finite multiset (represented as a `List`) of `m`
   subsets of a finite set `U` with `|U| < m`, then there exists a nonempty sub-multiset `I`
   of `C` (`I.Sublist C`, `I ≠ []`) whose common intersection has cardinality `|I| - 1`.
2. `bouchard_question_2_2`: If `F` is a finite multiset of subsets of `Fin M` satisfying
   `|⋃ F| + 1 < |F|`, then there exists a nonempty proper sub-multiset `F'` (`F'.Sublist F`,
   `F' ≠ []`, `F'.length < F.length`) such that `|F| - |F'| = |⋃ F'| + 1`.
-/

namespace BouchardQ22

/-- Cardinality of a Boolean predicate on `Fin N`. -/
def card {N : Nat} (S : Fin N → Bool) : Nat :=
  (List.finRange N).countP S

/-- Common intersection of a list of subsets inside a universe `U`. -/
def commonInter {N : Nat} (U : Fin N → Bool) (I : List (Fin N → Bool)) : Fin N → Bool :=
  fun y => U y && I.all (fun S => S y)

/-- Union of all sets in a list. -/
def unionAll {N : Nat} (F : List (Fin N → Bool)) : Fin N → Bool :=
  fun y => F.any (fun S => S y)

/-- Sum of a `Nat`-valued function over a list. -/
def sumList {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | a :: t, f => f a + sumList t f

/-- Product of cardinalities of sets in a list. -/
def prodCard {N : Nat} : List (Fin N → Bool) → Nat
  | [] => 1
  | S :: t => card S * prodCard t

/-! ## Elementary List & Counting Helpers -/

theorem sumList_const {α : Type} (l : List α) (c : Nat) :
    sumList l (fun _ => c) = l.length * c := by
  induction l with
  | nil => simp [sumList]
  | cons a t ih =>
    simp [sumList, ih, Nat.succ_mul]
    omega

theorem sumList_add {α : Type} (l : List α) (f g : α → Nat) :
    sumList l (fun x => f x + g x) = sumList l f + sumList l g := by
  induction l with
  | nil => simp [sumList]
  | cons a t ih =>
    simp [sumList, ih]
    omega

theorem sumList_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    sumList xs (fun x => sumList ys (fun y => f x y)) =
    sumList ys (fun y => sumList xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    simp only [sumList]
    have h0 := sumList_const ys 0
    simp only [Nat.mul_zero] at h0
    exact h0.symm
  | cons x xt ihx =>
    simp [sumList, ihx, sumList_add]

theorem sumList_le {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) : sumList l f ≤ sumList l g := by
  induction l with
  | nil => simp [sumList]
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp [sumList]
    omega

theorem sumList_mul_left {α : Type} (l : List α) (c : Nat) (f : α → Nat) :
    sumList l (fun x => c * f x) = c * sumList l f := by
  induction l with
  | nil => simp [sumList]
  | cons a t ih =>
    simp [sumList, ih, Nat.mul_add]

theorem sumList_if_countP {α : Type} (l : List α) (p : α → Bool) (c : Nat) :
    sumList l (fun x => if p x then c else 0) = l.countP p * c := by
  induction l with
  | nil => simp [sumList]
  | cons a t ih =>
    cases hp : p a <;> simp [sumList, hp, ih, Nat.succ_mul] <;> omega

theorem sumList_filter {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) :
    sumList (l.filter p) f = sumList l (fun x => if p x then f x else 0) := by
  induction l with
  | nil => simp [sumList]
  | cons a t ih =>
    cases hp : p a <;> simp [hp, sumList, ih]

theorem exists_gt_of_sumList_gt {α : Type} (l : List α) (f : α → Nat) (c : Nat)
    (h : l.length * c < sumList l f) : ∃ x ∈ l, c < f x := by
  induction l with
  | nil => simp [sumList] at h
  | cons a t ih =>
    simp [sumList, Nat.succ_mul] at h
    by_cases ha : c < f a
    · exact ⟨a, List.mem_cons_self .., ha⟩
    · have htail : t.length * c < sumList t f := by omega
      obtain ⟨x, hx, hfx⟩ := ih htail
      exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩

theorem countP_congr {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp [List.countP_cons, ha, ht]

theorem countP_mono {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) : l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    cases hp : p a
    · simp [List.countP_cons, hp]
      cases q a <;> simp <;> omega
    · have hq := h a (List.mem_cons_self ..) hp
      simp [hp, hq]
      omega

theorem countP_filter_eq {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter p).countP q = l.countP (fun x => p x && q x) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq, ih]

theorem countP_add_compl {α : Type} (l : List α) (U F : α → Bool) :
    l.countP (fun y => U y && !F y) + l.countP (fun y => U y && F y) = l.countP U := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hU : U a <;> cases hF : F a <;> simp [hU, hF] <;> omega

theorem countP_remove_one {α : Type} [DecidableEq α] (l : List α) (hnd : l.Nodup)
    (S : α → Bool) (x : α) (hx : x ∈ l) (hSx : S x = true) :
    l.countP (fun y => S y && decide (y ≠ x)) + 1 = l.countP S := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨ha_notin, ht_nd⟩
    by_cases hax : a = x
    · subst hax
      have hcongr : t.countP (fun y => S y && decide (y ≠ a)) = t.countP S := by
        apply countP_congr
        intro y hy
        have hne : y ≠ a := fun heq => ha_notin (heq ▸ hy)
        simp [hne]
      rw [List.countP_cons, List.countP_cons, hcongr, hSx]
      simp
    · have hxt : x ∈ t := by
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact absurd rfl hax
        · exact hmem
      have hih := ih ht_nd hxt
      simp [List.countP_cons, hax]
      cases S a <;> simp <;> omega

theorem card_remove_one {N : Nat} (S : Fin N → Bool) (x : Fin N) (hSx : S x = true) :
    card (fun y => S y && decide (y ≠ x)) + 1 = card S := by
  exact countP_remove_one (List.finRange N) (List.nodup_finRange N) S x (List.mem_finRange x) hSx

theorem prodCard_pos {N : Nat} (C : List (Fin N → Bool))
    (hpos : ∀ S ∈ C, 0 < card S) : 0 < prodCard C := by
  induction C with
  | nil => simp [prodCard]
  | cons S t ih =>
    have hS := hpos S (List.mem_cons_self ..)
    have ht := ih (fun T hT => hpos T (List.mem_cons_of_mem S hT))
    simp [prodCard]
    exact Nat.mul_pos hS ht

theorem card_dvd_prodCard {N : Nat} (C : List (Fin N → Bool)) (S : Fin N → Bool)
    (hS : S ∈ C) : card S ∣ prodCard C := by
  induction C with
  | nil => simp at hS
  | cons T t ih =>
    rcases List.mem_cons.mp hS with rfl | hmem
    · exact Nat.dvd_mul_right (card S) (prodCard t)
    · exact Nat.dvd_trans (ih hmem) (Nat.dvd_mul_left (prodCard t) (card T))

theorem sublist_map_lift {α β : Type} (f : α → β) {l : List α} {m : List β}
    (h : m.Sublist (l.map f)) : ∃ k : List α, k.Sublist l ∧ k.map f = m := by
  induction l generalizing m with
  | nil =>
    cases h
    exact ⟨[], List.Sublist.slnil, rfl⟩
  | cons a t ih =>
    simp only [List.map_cons] at h
    cases h with
    | cons _ hsub =>
      obtain ⟨k, hk, hmap⟩ := ih hsub
      exact ⟨k, List.Sublist.cons a hk, hmap⟩
    | cons_cons _ hsub =>
      obtain ⟨k, hk, hmap⟩ := ih hsub
      exact ⟨a :: k, List.Sublist.cons_cons a hk, by simp [hmap]⟩

theorem sublist_append_split {α : Type} {l1 l2 k : List α}
    (h : k.Sublist (l1 ++ l2)) :
    ∃ k1 k2 : List α, k = k1 ++ k2 ∧ k1.Sublist l1 ∧ k2.Sublist l2 := by
  induction l1 generalizing k with
  | nil =>
    exact ⟨[], k, rfl, List.Sublist.slnil, h⟩
  | cons a t ih =>
    simp only [List.cons_append] at h
    cases h with
    | cons _ hsub =>
      obtain ⟨k1, k2, hk, h1, h2⟩ := ih hsub
      exact ⟨k1, k2, hk, List.Sublist.cons a h1, h2⟩
    | cons_cons _ hsub =>
      obtain ⟨k1, k2, hk, h1, h2⟩ := ih hsub
      exact ⟨a :: k1, k2, by simp [hk], List.Sublist.cons_cons a h1, h2⟩

theorem card_zero_implies_false {N : Nat} (S : Fin N → Bool) (h0 : card S = 0) (y : Fin N) :
    S y = false := by
  cases hSy : S y
  · rfl
  · have hpos := card_remove_one S y hSy
    omega

/-! ## Main Theorem 1: The 6-Line Weight-Distribution Induction Lemma -/

theorem intersection_witness_aux {N : Nat} (u : Nat) :
    ∀ (U : Fin N → Bool) (C : List (Fin N → Bool)),
      card U = u →
      (∀ S ∈ C, ∀ y, S y = true → U y = true) →
      card U < C.length →
      ∃ I : List (Fin N → Bool),
        I.Sublist C ∧ I ≠ [] ∧ card (commonInter U I) + 1 = I.length := by
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro U C hU_eq hsub hlt
    -- Case 1: some set in C is empty
    by_cases hempty : ∃ S ∈ C, card S = 0
    · obtain ⟨S, hSC, hS0⟩ := hempty
      refine ⟨[S], List.singleton_sublist.mpr hSC, by simp, ?_⟩
      have hci0 : card (commonInter U [S]) = 0 := by
        have hle : card (commonInter U [S]) ≤ card S := by
          apply countP_mono
          intro y _ hy
          simp [commonInter] at hy
          exact hy.2
        omega
      simp [hci0]
    · -- Case 2: every set in C is nonempty
      have hpos : ∀ S ∈ C, 0 < card S := by
        intro S hSC
        by_cases h0 : card S = 0
        · exact absurd ⟨S, hSC, h0⟩ hempty
        · omega
      let P := prodCard C
      have hP_pos : 0 < P := prodCard_pos C hpos
      let Ulist := (List.finRange N).filter U
      have hUlist_len : Ulist.length = card U := by
        simp only [Ulist, card]
        have hlen_f : ∀ l : List (Fin N), (l.filter U).length = l.countP U := by
          intro l
          induction l with
          | nil => rfl
          | cons a t iht =>
            cases hUa : U a <;> simp [hUa, iht]
        exact hlen_f (List.finRange N)
      let weight : Fin N → Nat := fun x => sumList C (fun S => if S x then P / card S else 0)
      -- Double counting: sum_{x ∈ U} weight(x) = C.length * P
      have hsum : sumList Ulist weight = C.length * P := by
        calc sumList Ulist weight
            = sumList C (fun S => sumList Ulist (fun x => if S x then P / card S else 0)) := by
              exact sumList_swap Ulist C (fun x S => if S x then P / card S else 0)
          _ = sumList C (fun S => Ulist.countP S * (P / card S)) := by
              have heq : ∀ l : List (Fin N → Bool),
                  sumList l (fun S => sumList Ulist (fun x => if S x then P / card S else 0)) =
                  sumList l (fun S => Ulist.countP S * (P / card S)) := by
                intro l
                induction l with
                | nil => rfl
                | cons a t iht => simp [sumList, sumList_if_countP]
              exact heq C
          _ = sumList C (fun _ => P) := by
              have hterm : ∀ l : List (Fin N → Bool),
                  (∀ S ∈ l, (∀ y, S y = true → U y = true) ∧ card S ∣ P) →
                  sumList l (fun S => Ulist.countP S * (P / card S)) = sumList l (fun _ => P) := by
                intro l hl
                induction l with
                | nil => rfl
                | cons S t iht =>
                  rcases hl S (List.mem_cons_self ..) with ⟨hSU, hdvd⟩
                  have hUcnt : Ulist.countP S = card S := by
                    simp only [Ulist, card, countP_filter_eq]
                    apply countP_congr
                    intro y _
                    cases hSy : S y
                    · simp
                    · simp [hSU y hSy]
                  have hmul : card S * (P / card S) = P := Nat.mul_div_cancel' hdvd
                  simp [sumList, hUcnt, hmul, iht (fun T hT => hl T (List.mem_cons_of_mem S hT))]
              exact hterm C (fun S hSC => ⟨hsub S hSC, card_dvd_prodCard C S hSC⟩)
          _ = C.length * P := sumList_const C P
      -- Pigeonhole: some x ∈ U receives weight > P
      have hgt : Ulist.length * P < sumList Ulist weight := by
        rw [hsum, hUlist_len]
        exact Nat.mul_lt_mul_of_pos_right hlt hP_pos
      obtain ⟨x, hxUlist, hwx⟩ := exists_gt_of_sumList_gt Ulist weight P hgt
      have hUx : U x = true := (List.mem_filter.mp hxUlist).2
      -- Filter sets containing x
      let J := C.filter (fun S => S x)
      have hJ_sub : J.Sublist C := List.filter_sublist
      have hwx_eq : weight x = sumList J (fun S => P / card S) := by
        simpa [weight, J] using (sumList_filter C (fun S => S x) (fun S => P / card S)).symm
      -- Some S₀ ∈ J has |S₀| < |J|
      have hex_small : ∃ S₀ ∈ J, card S₀ < J.length := by
        by_cases hex : ∃ S₀ ∈ J, card S₀ < J.length
        · exact hex
        · exfalso
          have hall : ∀ S ∈ J, J.length ≤ card S := by
            intro S hSJ
            by_cases hltS : card S < J.length
            · exact absurd ⟨S, hSJ, hltS⟩ hex
            · omega
          have hJpos : 0 < J.length := by
            cases hJ : J with
            | nil =>
              rw [hJ] at hwx_eq
              simp [sumList] at hwx_eq
              omega
            | cons _ _ => simp
          have hsum_le : J.length * sumList J (fun S => P / card S) ≤ J.length * P := by
            calc J.length * sumList J (fun S => P / card S)
                = sumList J (fun S => J.length * (P / card S)) := (sumList_mul_left J J.length _).symm
              _ ≤ sumList J (fun _ => P) := by
                  apply sumList_le
                  intro S hSJ
                  have hSC : S ∈ C := hJ_sub.subset hSJ
                  have hdvd : card S ∣ P := card_dvd_prodCard C S hSC
                  have hle : J.length ≤ card S := hall S hSJ
                  calc J.length * (P / card S)
                      ≤ card S * (P / card S) := Nat.mul_le_mul_right _ hle
                    _ = P := Nat.mul_div_cancel' hdvd
              _ = J.length * P := sumList_const J P
          have hle_P : weight x ≤ P := by
            rw [hwx_eq]
            exact Nat.le_of_mul_le_mul_left hsum_le hJpos
          omega
      obtain ⟨S₀, hS₀J, hS₀_lt⟩ := hex_small
      have hS₀x : S₀ x = true := (List.mem_filter.mp hS₀J).2
      have hS₀C : S₀ ∈ C := hJ_sub.subset hS₀J
      obtain ⟨J1, J2, hJ_split⟩ := List.append_of_mem hS₀J
      let Jrem := J1 ++ J2
      -- Define smaller universe U' = S₀ \ {x} and projected sets C'
      let U' : Fin N → Bool := fun y => S₀ y && decide (y ≠ x)
      have hcardU'_succ : card U' + 1 = card S₀ := card_remove_one S₀ x hS₀x
      have hcardS₀_le : card S₀ ≤ card U := by
        apply countP_mono
        intro y _ hy
        exact hsub S₀ hS₀C y hy
      have hcardU'_lt_u : card U' < u := by omega
      let proj : (Fin N → Bool) → (Fin N → Bool) := fun S y => S y && U' y
      let C' := Jrem.map proj
      have hJrem_len : Jrem.length + 1 = J.length := by
        simp [Jrem, hJ_split]
        omega
      have hcardU'_lt_C' : card U' < C'.length := by
        simp [C']
        omega
      have hC'_sub : ∀ T ∈ C', ∀ y, T y = true → U' y = true := by
        intro T hT y hy
        obtain ⟨S, _, rfl⟩ := List.mem_map.mp hT
        simp [proj] at hy
        exact hy.2
      -- Apply strong induction to (U', C')
      obtain ⟨I', hI'_sub, hI'_ne, hI'_card⟩ :=
        ih (card U') hcardU'_lt_u U' C' rfl hC'_sub hcardU'_lt_C'
      obtain ⟨K, hK_sub, hK_map⟩ := sublist_map_lift proj hI'_sub
      obtain ⟨K1, K2, hK_eq, hK1_sub, hK2_sub⟩ := sublist_append_split hK_sub
      let I := K1 ++ S₀ :: K2
      -- I is a nonempty sublist of C
      have hI_sub_J : I.Sublist J := by
        rw [hJ_split]
        exact List.Sublist.append hK1_sub (List.Sublist.cons_cons S₀ hK2_sub)
      have hI_sub_C : I.Sublist C := hI_sub_J.trans hJ_sub
      have hI_ne : I ≠ [] := by
        intro hnil
        have : S₀ ∈ I := by simp [I]
        rw [hnil] at this
        simp at this
      have hK_ne : K ≠ [] := by
        intro hnil
        rw [hnil] at hK_map
        exact hI'_ne hK_map.symm
      -- Every set in I contains x, so x ∈ commonInter U I
      have hIx : commonInter U I x = true := by
        simp only [commonInter, hUx, Bool.true_and, List.all_eq_true]
        intro S hSI
        have hSJ : S ∈ J := hI_sub_J.subset hSI
        exact (List.mem_filter.mp hSJ).2
      -- Removing x from commonInter U I yields exact pointwise equality with commonInter U' I'
      have hci_eq : ∀ y : Fin N,
          (commonInter U I y && decide (y ≠ x)) = commonInter U' I' y := by
        intro y
        by_cases hyx : y = x
        · subst hyx
          simp [U', commonInter]
        · have hU'y : U' y = S₀ y := by simp [U', hyx]
          -- Compute LHS
          have hL : (commonInter U I y && decide (y ≠ x)) = (S₀ y && K.all (fun S => S y)) := by
            simp only [commonInter, hyx, ne_eq, not_false_eq_true, decide_true, Bool.and_true,
              I, hK_eq, List.all_append, List.all_cons]
            cases hS₀y : S₀ y
            · simp
            · have hUy : U y = true := hsub S₀ hS₀C y hS₀y
              simp [hUy]
          -- Compute RHS
          have hR : commonInter U' I' y = (S₀ y && K.all (fun S => S y)) := by
            rw [← hK_map]
            simp only [commonInter, hU'y]
            cases hS₀y : S₀ y
            · simp
            · simp only [Bool.true_and]
              have hmap_all : ∀ L : List (Fin N → Bool),
                  (L.map proj).all (fun T => T y) = L.all (fun S => S y) := by
                intro L
                induction L with
                | nil => rfl
                | cons a t iht =>
                  simp only [List.map_cons, List.all_cons, proj, hU'y, hS₀y, Bool.and_true, iht]
              exact hmap_all K
          rw [hL, hR]
      have hcard_inter : card (commonInter U I) = card (commonInter U' I') + 1 := by
        have hrem := card_remove_one (commonInter U I) x hIx
        have hcongr : card (fun y => commonInter U I y && decide (y ≠ x)) = card (commonInter U' I') := by
          apply countP_congr
          intro y _
          exact hci_eq y
        omega
      have hlen_I : I.length = I'.length + 1 := by
        have h1 : I.length = K.length + 1 := by
          simp [I, hK_eq]
          omega
        have h2 : I'.length = K.length := by
          rw [← hK_map, List.length_map]
        omega
      refine ⟨I, hI_sub_C, hI_ne, ?_⟩
      omega

/-- Main Lemma: If `m > |U|`, some nonempty sub-multiset `I` has `|⋂ I| = |I| - 1`. -/
theorem intersection_witness_lemma {N : Nat} (U : Fin N → Bool) (C : List (Fin N → Bool))
    (hsub : ∀ S ∈ C, ∀ y, S y = true → U y = true)
    (hlt : card U < C.length) :
    ∃ I : List (Fin N → Bool),
      I.Sublist C ∧ I ≠ [] ∧ card (commonInter U I) + 1 = I.length :=
  intersection_witness_aux (card U) U C rfl hsub hlt

/-! ## Main Theorem 2: Affirmative Solution to Bouchard's Question 2.2 -/

/-- Lift a subset of `Fin M` to `Fin (M + k)` by padding with `false`. -/
def padSet {M k : Nat} (S : Fin M → Bool) : Fin (M + k) → Bool :=
  fun y => if h : y.val < M then S ⟨y.val, h⟩ else false

theorem card_padSet {M k : Nat} (S : Fin M → Bool) :
    card (padSet (k := k) S) = card S := by
  simp only [card]
  have hsplit : ∀ (n : Nat) (f : Fin n → Bool) (d : Nat),
      (List.finRange (n + d)).countP (fun y => if h : y.val < n then f ⟨y.val, h⟩ else false) =
      (List.finRange n).countP f := by
    intro n f d
    induction d with
    | zero =>
      apply countP_congr
      intro y _
      simp
    | succ d ih =>
      have hlast : List.finRange (n + (d + 1)) =
          (List.finRange (n + d)).map Fin.castSucc ++ [Fin.last (n + d)] :=
        List.finRange_succ_last
      rw [hlast, List.countP_append, List.countP_map]
      have hflast : ([Fin.last (n + d)] : List (Fin (n + (d + 1)))).countP
          (fun y => if h : y.val < n then f ⟨y.val, h⟩ else false) = 0 := by
        have hnot : ¬ (n + d < n) := by omega
        simp [Fin.last, hnot]
      have hhead : (List.finRange (n + d)).countP
          ((fun y : Fin (n + (d + 1)) => if h : y.val < n then f ⟨y.val, h⟩ else false) ∘ Fin.castSucc) =
          (List.finRange n).countP f := by
        simpa [Function.comp_def, Fin.castSucc] using ih
      rw [hhead, hflast]
      omega
  exact hsplit M S k

theorem card_padUniverse {M k : Nat} (U0 : Fin M → Bool) :
    card (fun y : Fin (M + k) => if h : y.val < M then U0 ⟨y.val, h⟩ else true) =
    card U0 + k := by
  simp only [card]
  induction k with
  | zero =>
    simp only [Nat.add_zero]
    apply countP_congr
    intro y _
    simp
  | succ d ih =>
    have hlast : List.finRange (M + (d + 1)) =
        (List.finRange (M + d)).map Fin.castSucc ++ [Fin.last (M + d)] :=
      List.finRange_succ_last
    rw [hlast, List.countP_append, List.countP_map]
    have hflast : ([Fin.last (M + d)] : List (Fin (M + (d + 1)))).countP
        (fun y => if h : y.val < M then U0 ⟨y.val, h⟩ else true) = 1 := by
      have hnot : ¬ (M + d < M) := by omega
      simp [Fin.last, hnot]
    have hhead : (List.finRange (M + d)).countP
        ((fun y : Fin (M + (d + 1)) => if h : y.val < M then U0 ⟨y.val, h⟩ else true) ∘ Fin.castSucc) =
        (List.finRange M).countP U0 + d := by
      simpa [Function.comp_def, Fin.castSucc] using ih
    rw [hhead, hflast]
    omega

/-- **Theorem (Affirmative Answer to Bouchard's Question 2.2, arXiv:2310.02482v2):**
For every finite multiset `F` of subsets of `Fin M` satisfying `|⋃ F| + 1 < |F|`,
there exists a nonempty proper sub-multiset `F'` (`F'.Sublist F`, `F' ≠ []`,
`F'.length < F.length`) such that `|F| - |F'| = |⋃ F'| + 1`. -/
theorem bouchard_question_2_2 {M : Nat} (F : List (Fin M → Bool))
    (hF : card (unionAll F) + 1 < F.length) :
    ∃ F' : List (Fin M → Bool),
      F'.Sublist F ∧ F' ≠ [] ∧ F'.length < F.length ∧
      F.length - F'.length = card (unionAll F') + 1 := by
  let u := card (unionAll F)
  let m := F.length
  let k := m - 2 - u
  -- Universe U of exact cardinality m - 2 containing ⋃ F
  let U : Fin (M + k) → Bool := fun y =>
    if h : y.val < M then unionAll F ⟨y.val, h⟩ else true
  have hcardU : card U = m - 2 := by
    have h := card_padUniverse (k := k) (unionAll F)
    show card U = m - 2
    rw [h]
    omega
  let complInU : (Fin M → Bool) → (Fin (M + k) → Bool) :=
    fun S y => U y && !padSet (k := k) S y
  let C := F.map complInU
  have hC_sub : ∀ T ∈ C, ∀ y, T y = true → U y = true := by
    intro T hT y hy
    obtain ⟨S, _, rfl⟩ := List.mem_map.mp hT
    simp [complInU] at hy
    exact hy.1
  have hC_lt : card U < C.length := by
    simp only [C, List.length_map, hcardU]
    omega
  obtain ⟨I, hI_sub, hI_ne, hI_card⟩ := intersection_witness_lemma U C hC_sub hC_lt
  obtain ⟨F', hF'_sub, hF'_map⟩ := sublist_map_lift complInU hI_sub
  have hF'_ne : F' ≠ [] := by
    intro hnil
    rw [hnil] at hF'_map
    exact hI_ne hF'_map.symm
  have hF'_len : F'.length = I.length := by
    rw [← hF'_map, List.length_map]
  -- De Morgan's law pointwise: commonInter U (F'.map complInU) y = U y && !padSet (unionAll F') y
  have hdemorgan : ∀ y : Fin (M + k),
      commonInter U I y = (U y && !padSet (k := k) (unionAll F') y) := by
    intro y
    rw [← hF'_map]
    simp only [commonInter]
    cases hUy : U y
    · simp
    · simp only [Bool.true_and]
      have hall : ∀ L : List (Fin M → Bool),
          (L.map complInU).all (fun T => T y) = !padSet (k := k) (unionAll L) y := by
        intro L
        induction L with
        | nil =>
          simp only [List.map_nil, List.all_nil, padSet, unionAll, List.any_nil]
          split <;> rfl
        | cons S t iht =>
          simp only [List.map_cons, List.all_cons, complInU, hUy, Bool.true_and]
          rw [iht]
          simp only [padSet, unionAll, List.any_cons]
          split
          · cases S ⟨y.val, ‹_›⟩ <;> cases t.any (fun T => T ⟨y.val, ‹_›⟩) <;> rfl
          · rfl
      exact hall F'
  -- Every element of padSet (unionAll F') lies in U
  have hU_and_pad : ∀ y : Fin (M + k),
      (U y && padSet (k := k) (unionAll F') y) = padSet (k := k) (unionAll F') y := by
    intro y
    simp only [U, padSet]
    split
    · rename_i hyM
      cases hfy : unionAll F' ⟨y.val, hyM⟩
      · simp
      · simp only [unionAll, List.any_eq_true] at hfy ⊢
        obtain ⟨S, hSF', hSy⟩ := hfy
        have hSF : S ∈ F := hF'_sub.subset hSF'
        have hUtrue : F.any (fun T => T ⟨y.val, hyM⟩) = true :=
          List.any_eq_true.mpr ⟨S, hSF, hSy⟩
        simp [hUtrue]
    · simp
  have hcard_sum : card (commonInter U I) + card (unionAll F') = card U := by
    have hcompl := countP_add_compl (List.finRange (M + k)) U (padSet (k := k) (unionAll F'))
    have h1 : (List.finRange (M + k)).countP (fun y => U y && !padSet (k := k) (unionAll F') y) =
        card (commonInter U I) := by
      simp only [card]
      apply countP_congr
      intro y _
      exact (hdemorgan y).symm
    have h2 : (List.finRange (M + k)).countP (fun y => U y && padSet (k := k) (unionAll F') y) =
        card (unionAll F') := by
      rw [← card_padSet (k := k) (unionAll F')]
      simp only [card]
      apply countP_congr
      intro y _
      exact hU_and_pad y
    rw [h1, h2] at hcompl
    exact hcompl
  refine ⟨F', hF'_sub, hF'_ne, ?_, ?_⟩ <;> omega

end BouchardQ22

#print axioms BouchardQ22.intersection_witness_lemma
#print axioms BouchardQ22.bouchard_question_2_2
