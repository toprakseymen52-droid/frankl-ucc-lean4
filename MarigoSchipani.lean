/-!
# Formal Disproof of Marigo & Schipani (2016) Conjectures 4.1–4.4 and Sharp Infimum-0 Theorem

Source: Francesco Marigo and Davide Schipani, "Remarks on Frankl's conjecture" (arXiv:1603.01215, 2016).

Zero external dependencies (pure Lean 4 core). Zero `sorry`, zero custom axioms.

Main results:
1. `cubeCoatoms_isReducedUnionClosed`: For all `k ≥ 1, s ≥ 2`, the "Cube + Coatoms" family
   `F_{k,s} = 2^[k] ∪ { [k] ∪ (Y \ {y}) : y ∈ Y } ∪ { [k] ∪ Y }` on `k + s` elements is
   a reduced union-closed family of size `2^k + s + 1`.
2. `marigo_schipani_conj_4_1_to_4_4_false`: Explicit `k = 5, s = 5` counterexample (`|S| = 10`,
   `|F| = 38`) violating Conjectures 4.1, 4.2, 4.3, and 4.4 directly on the literal sums over
   all `38 × 38` pairs (`5090 < 5130`, `2545 < 2585`, `7635 < 7715`).
3. `marigo_schipani_infimum_zero`: For every fixed integer `r ≥ 1` and every `M ≥ 1`, there
   exists a reduced union-closed family `F` such that
   `M * (2 * ∑ f_x^{r+1}) < |F| * (∑ f_x^r)`, proving `inf = 0` for every fixed `r ≥ 1`.
-/

namespace MarigoSchipani

/-! ## Definitions matching arXiv:1603.01215 -/

/-- A reduced union-closed family on `Fin n` (Marigo & Schipani, Section 2):
distinct subsets, containing `∅` and `S`, union-closed, and for every `x ∈ S`
there exist `A, B ∈ F` with `A \ B = {x}`. -/
def isReducedUnionClosed {n : Nat} (F : List (Fin n → Bool)) : Prop :=
  F.Nodup ∧
  (fun _ => false) ∈ F ∧
  (fun _ => true) ∈ F ∧
  (∀ A ∈ F, ∀ B ∈ F, (fun i => A i || B i) ∈ F) ∧
  (∀ x : Fin n, ∃ A ∈ F, ∃ B ∈ F, ∀ y : Fin n, (A y && !B y) = decide (y = x))

def card {n : Nat} (A : Fin n → Bool) : Nat :=
  (List.finRange n).countP A

def freq {n : Nat} (F : List (Fin n → Bool)) (x : Fin n) : Nat :=
  F.countP (fun A => A x)

def sumList {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | a :: t, f => f a + sumList t f

def sumCard {n : Nat} (F : List (Fin n → Bool)) : Nat :=
  sumList F card

def sumInter {n : Nat} (F : List (Fin n → Bool)) : Nat :=
  sumList F (fun A => sumList F (fun B => card (fun i => A i && B i)))

def sumDiff {n : Nat} (F : List (Fin n → Bool)) : Nat :=
  sumList F (fun A => sumList F (fun B => card (fun i => A i && !B i)))

def sumUnion {n : Nat} (F : List (Fin n → Bool)) : Nat :=
  sumList F (fun A => sumList F (fun B => card (fun i => A i || B i)))

def sumFreqPow {n : Nat} (F : List (Fin n → Bool)) (r : Nat) : Nat :=
  sumList (List.finRange n) (fun x => (freq F x) ^ r)

/-! ## Elementary Helpers -/

theorem nodup_map_inj {α β : Type} (f : α → β) (hf : ∀ x y, f x = f y → x = y)
    {l : List α} (hnd : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2⟩
    intro hmem
    obtain ⟨b, hbt, hfb⟩ := List.mem_map.mp hmem
    have hab : b = a := hf b a hfb
    subst hab
    exact hnd.1 hbt

theorem nodup_append_disjoint {α : Type} {l1 l2 : List α}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hdisj : ∀ x ∈ l1, x ∉ l2) :
    (l1 ++ l2).Nodup := by
  induction l1 with
  | nil => simpa using h2
  | cons a t ih =>
    rw [List.nodup_cons] at h1
    simp only [List.cons_append, List.nodup_cons]
    refine ⟨?_, ih h1.2 (fun x hx => hdisj x (List.mem_cons_of_mem a hx))⟩
    intro hmem
    rcases List.mem_append.mp hmem with hat | ha2
    · exact h1.1 hat
    · exact hdisj a (List.mem_cons_self ..) ha2

theorem countP_map_const {α β : Type} (l : List α) (f : α → β) (p : β → Bool) (b : Bool)
    (h : ∀ x ∈ l, p (f x) = b) :
    (l.map f).countP p = if b then l.length else 0 := by
  induction l with
  | nil => cases b <;> simp
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    cases b <;> simp [ha, ht] <;> omega

theorem countP_congr {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp [List.countP_cons, ha, ht]

theorem sumList_append {α : Type} (l1 l2 : List α) (f : α → Nat) :
    sumList (l1 ++ l2) f = sumList l1 f + sumList l2 f := by
  induction l1 with
  | nil => simp [sumList]
  | cons a t ih => simp [sumList, ih]; omega

theorem sumList_map {α β : Type} (l : List α) (g : α → β) (f : β → Nat) :
    sumList (l.map g) f = sumList l (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [sumList, ih]

theorem sumList_const {α : Type} (l : List α) (c : Nat) :
    sumList l (fun _ => c) = l.length * c := by
  induction l with
  | nil => simp [sumList]
  | cons a t ih => simp [sumList, ih, Nat.succ_mul]; omega

theorem sumList_congr {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x = g x) : sumList l f = sumList l g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp [sumList, ha, ht]

/-! ## Complete Boolean Cube `allBools k` -/

def liftBit {m : Nat} (bit : Bool) (S : Fin m → Bool) : Fin (m + 1) → Bool :=
  fun i => if h : i.val < m then S ⟨i.val, h⟩ else bit

theorem liftBit_inj {m : Nat} (bit : Bool) {S T : Fin m → Bool}
    (h : liftBit bit S = liftBit bit T) : S = T := by
  funext i
  have hi := congrFun h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  simpa [liftBit, i.isLt] using hi

theorem liftBit_false_ne_true {m : Nat} (S T : Fin m → Bool) :
    liftBit false S ≠ liftBit true T := by
  intro h
  have hlast := congrFun h (Fin.last m)
  simp [liftBit, Fin.last] at hlast

/-- Canonical enumeration of all `2^k` subsets of `Fin k`. -/
def allBools : (k : Nat) → List (Fin k → Bool)
  | 0 => [fun i => Fin.elim0 i]
  | k + 1 => (allBools k).map (liftBit false) ++ (allBools k).map (liftBit true)

theorem allBools_length (k : Nat) : (allBools k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [allBools, ih, Nat.pow_succ]
    omega

theorem allBools_nodup (k : Nat) : (allBools k).Nodup := by
  induction k with
  | zero => simp [allBools]
  | succ k ih =>
    simp only [allBools]
    apply nodup_append_disjoint
    · exact nodup_map_inj (liftBit false) (fun _ _ => liftBit_inj false) ih
    · exact nodup_map_inj (liftBit true) (fun _ _ => liftBit_inj true) ih
    · intro x hx1 hx2
      obtain ⟨S, _, rfl⟩ := List.mem_map.mp hx1
      obtain ⟨T, _, hEq⟩ := List.mem_map.mp hx2
      exact liftBit_false_ne_true S T hEq.symm

theorem mem_allBools {k : Nat} (S : Fin k → Bool) : S ∈ allBools k := by
  induction k with
  | zero =>
    simp only [allBools, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ k ih =>
    let S' : Fin k → Bool := fun j => S ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
    have hS' : S' ∈ allBools k := ih S'
    have hEq : S = liftBit (S (Fin.last k)) S' := by
      funext i
      simp only [liftBit, S']
      split
      · rfl
      · have hi : i = Fin.last k := Fin.ext (by simp [Fin.last]; omega)
        rw [hi]
    rw [hEq]
    cases S (Fin.last k)
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨S', hS', rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨S', hS', rfl⟩)

theorem allBools_freq {k : Nat} (hk : 1 ≤ k) (x : Fin k) :
    (allBools k).countP (fun S => S x) = 2 ^ (k - 1) := by
  induction k with
  | zero => omega
  | succ m ih =>
    simp only [allBools, List.countP_append, Nat.add_sub_cancel]
    by_cases hxm : x.val < m
    · have hm1 : 1 ≤ m := by omega
      have h0 : ((allBools m).map (liftBit false)).countP (fun S => S x) =
          (allBools m).countP (fun S => S ⟨x.val, hxm⟩) := by
        rw [List.countP_map]
        apply countP_congr
        intro S _
        simp [liftBit, hxm]
      have h1 : ((allBools m).map (liftBit true)).countP (fun S => S x) =
          (allBools m).countP (fun S => S ⟨x.val, hxm⟩) := by
        rw [List.countP_map]
        apply countP_congr
        intro S _
        simp [liftBit, hxm]
      rw [h0, h1, ih hm1 ⟨x.val, hxm⟩]
      have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
        conv => lhs; rw [show m = (m - 1) + 1 by omega]
        exact Nat.pow_succ 2 (m - 1)
      omega
    · have hxeq : x = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
      rw [hxeq]
      have h0 : ((allBools m).map (liftBit false)).countP (fun S => S (Fin.last m)) = 0 := by
        simpa using countP_map_const (allBools m) (liftBit false) (fun S => S (Fin.last m)) false
          (fun S _ => by simp [liftBit, Fin.last])
      have h1 : ((allBools m).map (liftBit true)).countP (fun S => S (Fin.last m)) =
          (allBools m).length := by
        simpa using countP_map_const (allBools m) (liftBit true) (fun S => S (Fin.last m)) true
          (fun S _ => by simp [liftBit, Fin.last])
      rw [h0, h1, allBools_length]
      omega

/-! ## The "Cube + Coatoms" Family `F_{k, s}` -/

def embedBot (k s : Nat) (S : Fin k → Bool) : Fin (k + s) → Bool :=
  fun i => if h : i.val < k then S ⟨i.val, h⟩ else false

def coatom (k s : Nat) (y : Fin s) : Fin (k + s) → Bool :=
  fun i => if i.val < k then true else decide (i.val ≠ k + y.val)

def cubeCoatoms (k s : Nat) : List (Fin (k + s) → Bool) :=
  (allBools k).map (embedBot k s) ++
  (List.finRange s).map (coatom k s) ++
  [fun _ => true]

theorem embedBot_inj (k s : Nat) {S T : Fin k → Bool}
    (h : embedBot k s S = embedBot k s T) : S = T := by
  funext i
  have hi := congrFun h ⟨i.val, by omega⟩
  simpa [embedBot, i.isLt] using hi

theorem coatom_inj (k s : Nat) {y1 y2 : Fin s}
    (h : coatom k s y1 = coatom k s y2) : y1 = y2 := by
  have h1 := congrFun h ⟨k + y1.val, by omega⟩
  have hnot : ¬ (k + y1.val < k) := by omega
  simp [coatom, hnot] at h1
  exact Fin.ext (by omega)

theorem embedBot_ne_coatom (k s : Nat) (hs : 2 ≤ s) (S : Fin k → Bool) (y : Fin s) :
    embedBot k s S ≠ coatom k s y := by
  intro h
  by_cases hy0 : y.val = 0
  · have hi := congrFun h ⟨k + 1, by omega⟩
    have hnot : ¬ (k + 1 < k) := by omega
    simp [embedBot, coatom, hnot, hy0] at hi
  · have hi := congrFun h ⟨k, by omega⟩
    have hnot : ¬ (k < k) := by omega
    simp [embedBot, coatom, hnot] at hi
    omega

theorem embedBot_ne_top (k s : Nat) (hs : 2 ≤ s) (S : Fin k → Bool) :
    embedBot k s S ≠ (fun _ => true) := by
  intro h
  have hi := congrFun h ⟨k, by omega⟩
  simp [embedBot] at hi

theorem coatom_ne_top (k s : Nat) (y : Fin s) :
    coatom k s y ≠ (fun _ => true) := by
  intro h
  have hi := congrFun h ⟨k + y.val, by omega⟩
  have hnot : ¬ (k + y.val < k) := by omega
  simp [coatom, hnot] at hi

theorem cubeCoatoms_length (k s : Nat) :
    (cubeCoatoms k s).length = 2 ^ k + s + 1 := by
  simp [cubeCoatoms, allBools_length]
  omega

theorem cubeCoatoms_isReducedUnionClosed (k s : Nat) (_hk : 1 ≤ k) (hs : 2 ≤ s) :
    isReducedUnionClosed (cubeCoatoms k s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Nodup
    simp only [cubeCoatoms]
    have h12 : ((allBools k).map (embedBot k s) ++ (List.finRange s).map (coatom k s)).Nodup := by
      apply nodup_append_disjoint
      · exact nodup_map_inj (embedBot k s) (fun _ _ => embedBot_inj k s) (allBools_nodup k)
      · exact nodup_map_inj (coatom k s) (fun _ _ => coatom_inj k s) (List.nodup_finRange s)
      · intro X hX1 hX2
        obtain ⟨S, _, rfl⟩ := List.mem_map.mp hX1
        obtain ⟨y, _, hEq⟩ := List.mem_map.mp hX2
        exact embedBot_ne_coatom k s hs S y hEq.symm
    apply nodup_append_disjoint h12 (by simp)
    intro X hX1 hX2
    rw [List.mem_singleton] at hX2
    rcases List.mem_append.mp hX1 with hbot | hco
    · obtain ⟨S, _, rfl⟩ := List.mem_map.mp hbot
      exact embedBot_ne_top k s hs S hX2
    · obtain ⟨y, _, rfl⟩ := List.mem_map.mp hco
      exact coatom_ne_top k s y hX2
  · -- ∅ ∈ F
    have hemp : (fun _ : Fin (k + s) => false) = embedBot k s (fun _ => false) := by
      funext i
      simp [embedBot]
    rw [hemp]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, mem_allBools _, rfl⟩))
  · -- S ∈ F
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · -- union-closed
    intro A hA B hB
    simp only [cubeCoatoms, List.mem_append, List.mem_singleton] at hA hB ⊢
    -- Helper: union with top is top
    have union_top_r : ∀ X : Fin (k + s) → Bool, (fun i => X i || true) = (fun _ => true) := by
      intro X; funext i; simp
    have union_top_l : ∀ X : Fin (k + s) → Bool, (fun i => true || X i) = (fun _ => true) := by
      intro X; funext i; simp
    rcases hA with (hAbot | hAco) | rfl
    · rcases hB with (hBbot | hBco) | rfl
      · obtain ⟨S, _, rfl⟩ := List.mem_map.mp hAbot
        obtain ⟨T, _, rfl⟩ := List.mem_map.mp hBbot
        left; left
        refine List.mem_map.mpr ⟨fun j => S j || T j, mem_allBools _, ?_⟩
        funext i; simp only [embedBot]; split <;> rfl
      · obtain ⟨S, _, rfl⟩ := List.mem_map.mp hAbot
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hBco
        left; right
        have hEq : (fun i => embedBot k s S i || coatom k s y i) = coatom k s y := by
          funext i; simp only [embedBot, coatom]; split <;> simp
        rw [hEq]
        exact List.mem_map.mpr ⟨y, hy, rfl⟩
      · right; exact union_top_r _
    · rcases hB with (hBbot | hBco) | rfl
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hAco
        obtain ⟨S, _, rfl⟩ := List.mem_map.mp hBbot
        left; right
        have hEq : (fun i => coatom k s y i || embedBot k s S i) = coatom k s y := by
          funext i; simp only [embedBot, coatom]; split <;> simp
        rw [hEq]
        exact List.mem_map.mpr ⟨y, hy, rfl⟩
      · obtain ⟨y1, hy1, rfl⟩ := List.mem_map.mp hAco
        obtain ⟨y2, _, rfl⟩ := List.mem_map.mp hBco
        by_cases hy : y1 = y2
        · subst hy
          left; right
          have hEq : (fun i => coatom k s y1 i || coatom k s y1 i) = coatom k s y1 := by
            funext i; simp
          rw [hEq]
          exact List.mem_map.mpr ⟨y1, hy1, rfl⟩
        · right
          funext i
          simp only [coatom]
          split
          · rfl
          · by_cases hi1 : i.val = k + y1.val
            · simp [hi1]
              exact fun h => hy (Fin.ext h)
            · simp [hi1]
      · right; exact union_top_r _
    · right; exact union_top_l _
  · -- reduced: ∀ x, ∃ A B ∈ F, A \ B = {x}
    intro x
    by_cases hxk : x.val < k
    · -- x ∈ [k]: take A = {x}, B = ∅
      let sing : Fin k → Bool := fun j => decide (j.val = x.val)
      refine ⟨embedBot k s sing,
        List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨sing, mem_allBools _, rfl⟩)),
        embedBot k s (fun _ => false),
        List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, mem_allBools _, rfl⟩)), ?_⟩
      intro y
      simp only [embedBot, sing]
      split
      · by_cases hyx : y = x
        · subst hyx; simp
        · have hne : y.val ≠ x.val := fun h => hyx (Fin.ext h)
          simp [hyx, hne]
      · have hyx : y ≠ x := fun h => by subst h; omega
        simp [hyx]
    · -- x ∈ Y: take A = S, B = coatom(x - k)
      let yx : Fin s := ⟨x.val - k, by omega⟩
      refine ⟨fun _ => true,
        List.mem_append_right _ (List.mem_singleton.mpr rfl),
        coatom k s yx,
        List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨yx, List.mem_finRange yx, rfl⟩)), ?_⟩
      intro y
      simp only [coatom, yx, Bool.true_and]
      split
      · have hyx : y ≠ x := fun h => by subst h; omega
        simp [hyx]
      · have hkx : k + (x.val - k) = x.val := by omega
        rw [hkx]
        by_cases hyx : y = x
        · subst hyx; simp
        · have hne : y.val ≠ x.val := fun h => hyx (Fin.ext h)
          simp [hyx, hne]

/-! ## Exact Frequencies and Power Sums of `cubeCoatoms k s` -/

theorem cubeCoatoms_freq_bot (k s : Nat) (hk : 1 ≤ k) (x : Fin (k + s)) (hx : x.val < k) :
    freq (cubeCoatoms k s) x = 2 ^ (k - 1) + s + 1 := by
  simp only [freq, cubeCoatoms, List.countP_append, List.countP_cons, List.countP_nil]
  have h1 : ((allBools k).map (embedBot k s)).countP (fun A => A x) = 2 ^ (k - 1) := by
    rw [List.countP_map]
    have hc : (allBools k).countP ((fun A => A x) ∘ embedBot k s) =
        (allBools k).countP (fun S => S ⟨x.val, hx⟩) := by
      apply countP_congr
      intro S _
      simp [embedBot, hx]
    rw [hc, allBools_freq hk ⟨x.val, hx⟩]
  have h2 : ((List.finRange s).map (coatom k s)).countP (fun A => A x) = s := by
    have h := countP_map_const (List.finRange s) (coatom k s) (fun A => A x) true
      (fun y _ => by simp [coatom, hx])
    simpa [List.length_finRange] using h
  rw [h1, h2]
  simp

theorem cubeCoatoms_freq_top (k s : Nat) (x : Fin (k + s)) (hx : k ≤ x.val) :
    freq (cubeCoatoms k s) x = s := by
  simp only [freq, cubeCoatoms, List.countP_append, List.countP_cons, List.countP_nil]
  have hnot : ¬ (x.val < k) := by omega
  have h1 : ((allBools k).map (embedBot k s)).countP (fun A => A x) = 0 := by
    simpa using countP_map_const (allBools k) (embedBot k s) (fun A => A x) false
      (fun S _ => by simp [embedBot, hnot])
  have h2 : ((List.finRange s).map (coatom k s)).countP (fun A => A x) = s - 1 := by
    rw [List.countP_map]
    let yx : Fin s := ⟨x.val - k, by omega⟩
    have hc : (List.finRange s).countP ((fun A => A x) ∘ coatom k s) =
        (List.finRange s).countP (fun y => decide (y ≠ yx)) := by
      apply countP_congr
      intro y _
      simp only [Function.comp_def, coatom, hnot, ite_false]
      by_cases hy : y = yx
      · subst hy
        have hval : x.val = k + yx.val := by simp [yx]; omega
        simp [hval]
      · have hne : x.val ≠ k + y.val := by
          intro h
          apply hy
          exact Fin.ext (by simp [yx]; omega)
        simp [hy, hne]
    rw [hc]
    have hsplit : ∀ (l : List (Fin s)), l.Nodup → yx ∈ l →
        l.countP (fun y => decide (y ≠ yx)) + 1 = l.length := by
      intro l hnd hmem
      induction l with
      | nil => simp at hmem
      | cons a t ih =>
        rw [List.nodup_cons] at hnd
        by_cases ha : a = yx
        · subst ha
          have ht : t.countP (fun y => decide (y ≠ yx)) = t.length := by
            have hc2 : t.countP (fun y => decide (y ≠ yx)) = t.countP (fun _ => true) := by
              apply countP_congr
              intro y hy
              have hne : y ≠ yx := fun h => hnd.1 (h ▸ hy)
              simp [hne]
            rw [hc2]; simp
          rw [List.countP_cons, ht]
          simp
        · have hxt : yx ∈ t := by
            rcases List.mem_cons.mp hmem with rfl | hm
            · exact absurd rfl ha
            · exact hm
          have hih := ih hnd.2 hxt
          simp [ha]
          omega
    have hsp := hsplit (List.finRange s) (List.nodup_finRange s) (List.mem_finRange yx)
    simp only [List.length_finRange] at hsp
    omega
  rw [h1, h2]
  have hs_pos : 1 ≤ s := by omega
  simp
  omega

theorem sumList_finRange_split (k s : Nat) (f : Fin (k + s) → Nat) (c1 c2 : Nat)
    (h1 : ∀ x : Fin (k + s), x.val < k → f x = c1)
    (h2 : ∀ x : Fin (k + s), k ≤ x.val → f x = c2) :
    sumList (List.finRange (k + s)) f = k * c1 + s * c2 := by
  induction s with
  | zero =>
    simp only [Nat.add_zero, Nat.zero_mul]
    have hc : sumList (List.finRange k) f = sumList (List.finRange k) (fun _ => c1) := by
      apply sumList_congr
      intro x _
      exact h1 x x.isLt
    rw [hc, sumList_const, List.length_finRange]
  | succ d ih =>
    have hlast : List.finRange (k + (d + 1)) =
        (List.finRange (k + d)).map Fin.castSucc ++ [Fin.last (k + d)] :=
      List.finRange_succ_last
    rw [hlast, sumList_append, sumList_map]
    have htail : sumList [Fin.last (k + d)] f = c2 := by
      simp only [sumList, Nat.add_zero]
      exact h2 (Fin.last (k + d)) (by simp [Fin.last])
    have hhead : sumList (List.finRange (k + d)) (fun x => f x.castSucc) = k * c1 + d * c2 := by
      exact ih (fun x => f x.castSucc)
        (fun x hx => h1 x.castSucc (by simpa using hx))
        (fun x hx => h2 x.castSucc (by simpa using hx))
    rw [hhead, htail, Nat.succ_mul]
    omega

theorem cubeCoatoms_sumFreqPow (k s r : Nat) (hk : 1 ≤ k) :
    sumFreqPow (cubeCoatoms k s) r = k * (2 ^ (k - 1) + s + 1) ^ r + s * s ^ r := by
  simp only [sumFreqPow]
  exact sumList_finRange_split k s
    (fun x => (freq (cubeCoatoms k s) x) ^ r)
    ((2 ^ (k - 1) + s + 1) ^ r) (s ^ r)
    (fun x hx => by rw [cubeCoatoms_freq_bot k s hk x hx])
    (fun x hx => by rw [cubeCoatoms_freq_top k s x hx])

/-! ## Theorem 1A: Explicit Counterexample `F_{5, 5}` to Conjectures 4.1–4.4 -/

def F_5_5 : List (Fin 10 → Bool) := cubeCoatoms 5 5

theorem F_5_5_isReducedUnionClosed : isReducedUnionClosed F_5_5 :=
  cubeCoatoms_isReducedUnionClosed 5 5 (by decide) (by decide)

/-- Direct kernel verification of the literal sums over all 38 × 38 ordered pairs of `F_{5, 5}`:
- `|F| = 38`, `∑ |A| = 135`, `∑ |A ∩ B| = 2545`, `∑ |A \ B| = 2585`, `∑ |A ∪ B| = 7715`
- Conjecture 4.1 fails: `2 * 2545 = 5090 < 5130 = 38 * 135`
- Conjectures 4.2 & 4.4 fail: `2545 < 2585`
- Conjecture 4.3 fails: `3 * 2545 = 7635 < 7715` -/
theorem marigo_schipani_conj_4_1_to_4_4_false :
    isReducedUnionClosed F_5_5 ∧
    F_5_5.length = 38 ∧
    2 * sumInter F_5_5 < F_5_5.length * sumCard F_5_5 ∧
    sumInter F_5_5 < sumDiff F_5_5 ∧
    3 * sumInter F_5_5 < sumUnion F_5_5 := by
  refine ⟨F_5_5_isReducedUnionClosed, by decide, by decide, by decide, by decide⟩

/-! ## Theorem 1B: Sharp Infimum-0 Theorem for Every Fixed `r ≥ 1` -/

theorem sq_lt_two_pow : ∀ n : Nat, 5 ≤ n → n * n < 2 ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm5 : m = 4
    · subst hm5; decide
    · have hm_ge : 5 ≤ m := by omega
      have hih := ih hm_ge
      have h2m : 2 * m + 1 < m * m := by
        have h1 : 5 * m ≤ m * m := Nat.mul_le_mul_right m hm_ge
        omega
      have hsq : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
        rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
        omega
      rw [hsq, Nat.pow_succ]
      omega

theorem nat_pow_mono_base {a b p : Nat} (h : a ≤ b) : a ^ p ≤ b ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.mul_le_mul ih h

/-- **Theorem (Sharp Infimum-0 for Every Fixed `r ≥ 1`):**
For every fixed integer `r ≥ 1` and every `M ≥ 1` (corresponding to any threshold `1 / M > 0`),
there exists a reduced union-closed family `F` on `Fin n` such that
`M * (2 * ∑_{x} f_x^{r+1}) < |F| * ∑_{x} f_x^r`. -/
theorem marigo_schipani_infimum_zero (r : Nat) (hr : 1 ≤ r) (M : Nat) (_hM : 1 ≤ M) :
    ∃ (n : Nat) (F : List (Fin n → Bool)),
      isReducedUnionClosed F ∧
      M * (2 * sumFreqPow F (r + 1)) < F.length * sumFreqPow F r := by
  let t : Nat := M * (2 * (r + 2) + 2) + 5
  let k : Nat := (r + 2) * t
  let s : Nat := 2 ^ ((r + 1) * t)
  have ht5 : 5 ≤ t := by omega
  have hk1 : 1 ≤ k := by
    have : 1 * 5 ≤ (r + 2) * t := Nat.mul_le_mul (by omega) ht5
    omega
  have hs2 : 2 ≤ s := by
    have hpow_ge : 1 ≤ (r + 1) * t := by
      have : 1 * 5 ≤ (r + 1) * t := Nat.mul_le_mul (by omega) ht5
      omega
    have h1 : 2 ^ 1 ≤ 2 ^ ((r + 1) * t) := Nat.pow_le_pow_right (by omega) hpow_ge
    simpa [s] using h1
  refine ⟨k + s, cubeCoatoms k s, cubeCoatoms_isReducedUnionClosed k s hk1 hs2, ?_⟩
  rw [cubeCoatoms_length, cubeCoatoms_sumFreqPow k s (r + 1) hk1, cubeCoatoms_sumFreqPow k s r hk1]
  -- Key relation 1: f_bot = 2^(k-1) + s + 1 ≤ 2^k
  have h2k_eq : 2 ^ k = s * 2 ^ t := by
    have hexp : k = (r + 1) * t + t := by
      simp only [k, Nat.add_mul, Nat.one_mul]
      omega
    rw [hexp, Nat.pow_add]
  have hfbot_le : 2 ^ (k - 1) + s + 1 ≤ 2 ^ k := by
    have h2km1 : 2 ^ k = 2 ^ (k - 1) * 2 := by
      conv => lhs; rw [show k = (k - 1) + 1 by omega]
      exact Nat.pow_succ 2 (k - 1)
    have h2t_ge : 4 ≤ 2 ^ t := by
      have h : 2 ^ 2 ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using h
    have hs_half : s + 1 ≤ 2 ^ (k - 1) := by
      have hmul : 4 * s ≤ s * 2 ^ t := by
        rw [Nat.mul_comm 4 s]
        exact Nat.mul_le_mul_left s h2t_ge
      omega
    omega
  -- Key relation 2: 2^(r*k) * 2^t = s^(r+1)
  have hexp_match : 2 ^ (r * k) * 2 ^ t = s ^ (r + 1) := by
    have hs_pow : s ^ (r + 1) = 2 ^ ((r + 1) * t * (r + 1)) := by
      simp only [s, ← Nat.pow_mul]
    rw [hs_pow, ← Nat.pow_add]
    congr 1
    have h1 : r * ((r + 2) * t) + t = (r * (r + 2) + 1) * t := by
      rw [← Nat.mul_assoc, Nat.add_mul, Nat.one_mul]
    have h2 : (r + 1) * t * (r + 1) = ((r + 1) * (r + 1)) * t := by
      rw [Nat.mul_right_comm]
    have h3 : r * (r + 2) + 1 = (r + 1) * (r + 1) := by
      rw [Nat.mul_add, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    simp only [k]
    rw [h1, h2, h3]
  -- Key relation 3: M * (2 * k + 2) < 2 ^ t
  have hM_bound : M * (2 * k + 2) < 2 ^ t := by
    have hstep1 : 2 * k + 2 ≤ (2 * (r + 2) + 2) * t := by
      have h2k_eq2 : 2 * k = 2 * (r + 2) * t := by
        simp only [k, Nat.mul_assoc]
      rw [h2k_eq2, Nat.add_mul]
      omega
    have hstep2 : M * (2 * k + 2) ≤ (M * (2 * (r + 2) + 2)) * t := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left M hstep1
    have hcoeff_lt : M * (2 * (r + 2) + 2) < t := by omega
    have hstep3 : (M * (2 * (r + 2) + 2)) * t < t * t :=
      Nat.mul_lt_mul_of_pos_right hcoeff_lt (by omega)
    have hstep4 : t * t < 2 ^ t := sq_lt_two_pow t ht5
    omega
  -- Upper bound numerator: 2 * (k * f_bot^(r+1) + s * s^(r+1)) ≤ 2 * k * (2^k)^(r+1) + 2 * (s * s^(r+1))
  have hnum_le : 2 * (k * (2 ^ (k - 1) + s + 1) ^ (r + 1) + s * s ^ (r + 1)) ≤
      2 * k * (2 ^ k) ^ (r + 1) + 2 * (s * s ^ (r + 1)) := by
    have hp := nat_pow_mono_base (p := r + 1) hfbot_le
    have hkm := Nat.mul_le_mul_left k hp
    rw [Nat.mul_add, Nat.mul_assoc 2 k]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hkm) _
  -- Exact identity: 2^t * (2 * k * (2^k)^(r+1) + 2 * (s * s^(r+1))) = (2 * k + 2) * (2^k * s^(r+1))
  have hpow_rk : (2 ^ k) ^ (r + 1) = 2 ^ k * 2 ^ (r * k) := by
    rw [← Nat.pow_mul, Nat.mul_add, Nat.mul_one, Nat.mul_comm k r, Nat.pow_add, Nat.mul_comm]
  have hscaled_num :
      2 ^ t * (2 * k * (2 ^ k) ^ (r + 1) + 2 * (s * s ^ (r + 1))) =
      (2 * k + 2) * (2 ^ k * s ^ (r + 1)) := by
    have hterm1 : 2 ^ t * (2 * k * (2 ^ k) ^ (r + 1)) = 2 * k * (2 ^ k * s ^ (r + 1)) := by
      rw [hpow_rk, ← hexp_match]
      ac_rfl
    have hterm2 : 2 ^ t * (2 * (s * s ^ (r + 1))) = 2 * (2 ^ k * s ^ (r + 1)) := by
      rw [h2k_eq]
      ac_rfl
    rw [Nat.mul_add, hterm1, hterm2, ← Nat.add_mul]
  -- Lower bound denominator: 2^k * s^(r+1) ≤ (2^k + s + 1) * (k * f_bot^r + s * s^r)
  have hden_ge : 2 ^ k * s ^ (r + 1) ≤
      (2 ^ k + s + 1) * (k * (2 ^ (k - 1) + s + 1) ^ r + s * s ^ r) := by
    have hs_eq : s * s ^ r = s ^ (r + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : 2 ^ k ≤ 2 ^ k + s + 1 := by omega
    have h2 : s ^ (r + 1) ≤ k * (2 ^ (k - 1) + s + 1) ^ r + s * s ^ r := by omega
    exact Nat.mul_le_mul h1 h2
  have hbase_pos : 0 < 2 ^ k * s ^ (r + 1) := by
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  -- Multiply by 2^t > 0 and compare
  have hscaled_lt :
      2 ^ t * (M * (2 * (k * (2 ^ (k - 1) + s + 1) ^ (r + 1) + s * s ^ (r + 1)))) <
      2 ^ t * ((2 ^ k + s + 1) * (k * (2 ^ (k - 1) + s + 1) ^ r + s * s ^ r)) := by
    calc 2 ^ t * (M * (2 * (k * (2 ^ (k - 1) + s + 1) ^ (r + 1) + s * s ^ (r + 1))))
        ≤ 2 ^ t * (M * (2 * k * (2 ^ k) ^ (r + 1) + 2 * (s * s ^ (r + 1)))) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left M hnum_le)
      _ = M * (2 ^ t * (2 * k * (2 ^ k) ^ (r + 1) + 2 * (s * s ^ (r + 1)))) := by ac_rfl
      _ = M * ((2 * k + 2) * (2 ^ k * s ^ (r + 1))) := by rw [hscaled_num]
      _ = (M * (2 * k + 2)) * (2 ^ k * s ^ (r + 1)) := by rw [Nat.mul_assoc]
      _ < 2 ^ t * (2 ^ k * s ^ (r + 1)) := Nat.mul_lt_mul_of_pos_right hM_bound hbase_pos
      _ ≤ 2 ^ t * ((2 ^ k + s + 1) * (k * (2 ^ (k - 1) + s + 1) ^ r + s * s ^ r)) :=
          Nat.mul_le_mul_left _ hden_ge
  exact Nat.lt_of_mul_lt_mul_left hscaled_lt

end MarigoSchipani

#print axioms MarigoSchipani.marigo_schipani_conj_4_1_to_4_4_false
#print axioms MarigoSchipani.marigo_schipani_infimum_zero
