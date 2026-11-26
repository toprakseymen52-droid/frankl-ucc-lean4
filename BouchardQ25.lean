/-!
# Formal Proof: Affirmative Answer to Bouchard's Open Question 2.5 Implies Frankl's Conjecture

Source: Christopher Bouchard, "Conjectures on union-closed families of sets" (arXiv:2310.02482v2, Sept 2024);
also listed as open on GEWU (math-orp-2370, Sept 8, 2026).

Zero external dependencies (pure Lean 4 core). Zero `sorry`, zero custom axioms.

Main result (`bouchard_q25_implies_frankl`):
If every finite union-closed family `A` on ground set `[n]` (`n ≥ 2`) satisfies
`UC_n A → UC_{n-1} A`, then every finite nontrivial union-closed family `B` satisfies
Frankl's Union-Closed Sets Conjecture (`∃ x, 2 * freq B x ≥ |B|`).
In fact, the doubling construction preserves `∅ ∈ B`, separating, and reduced properties as well.
-/

namespace BouchardQ25

/-- A finite union-closed family on exact ground set `Fin n` (distinct finite sets, nonempty family,
every ground element appears in at least one member). -/
def isUnionClosed {n : Nat} (A : List (Fin n → Bool)) : Prop :=
  A ≠ [] ∧
  A.Nodup ∧
  (∀ S ∈ A, ∀ T ∈ A, (fun i => S i || T i) ∈ A) ∧
  (∀ i : Fin n, ∃ S ∈ A, S i = true)

/-- Number of sets in `A` containing element `x`. -/
def freq {n : Nat} (A : List (Fin n → Bool)) (x : Fin n) : Nat :=
  A.countP (fun S => S x)

/-- Number of sets in `A` disjoint from `{x}`. -/
def notFreq {n : Nat} (A : List (Fin n → Bool)) (x : Fin n) : Nat :=
  A.countP (fun S => !S x)

/-- Number of sets in `A` containing both `a` and `b`. -/
def containsPair {n : Nat} (A : List (Fin n → Bool)) (a b : Fin n) : Nat :=
  A.countP (fun S => S a && S b)

/-- Number of sets in `A` disjoint from `{a, b}`. -/
def disjointPair {n : Nat} (A : List (Fin n → Bool)) (a b : Fin n) : Nat :=
  A.countP (fun S => !S a && !S b)

/-- Bouchard's rung `UC_n`: there exists a singleton `{x}` with `|A_{x}| ≥ |A_{¬x}|` (Frankl's conjecture). -/
def UC_n {n : Nat} (A : List (Fin n → Bool)) : Prop :=
  ∃ x : Fin n, freq A x ≥ notFreq A x

/-- Bouchard's rung `UC_{n-1}`: there exists a 2-element set `{a, b}` with `|A_{a,b}| ≥ |A_{¬{a,b}}|`. -/
def UC_n_minus_1 {n : Nat} (A : List (Fin n → Bool)) : Prop :=
  ∃ a b : Fin n, a ≠ b ∧ containsPair A a b ≥ disjointPair A a b

/-! ## Elementary Counting Identities -/

theorem freq_add_notFreq {n : Nat} (A : List (Fin n → Bool)) (x : Fin n) :
    freq A x + notFreq A x = A.length := by
  induction A with
  | nil => simp [freq, notFreq]
  | cons S t ih =>
    simp only [freq, notFreq, List.countP_cons, List.length_cons] at ih ⊢
    cases S x <;> simp <;> omega

theorem pair_identity {n : Nat} (A : List (Fin n → Bool)) (a b : Fin n) :
    freq A a + freq A b + disjointPair A a b = A.length + containsPair A a b := by
  induction A with
  | nil => simp [freq, containsPair, disjointPair]
  | cons S t ih =>
    simp only [freq, containsPair, disjointPair, List.countP_cons, List.length_cons] at ih ⊢
    cases S a <;> cases S b <;> simp <;> omega

theorem UC_n_iff_half {n : Nat} (A : List (Fin n → Bool)) :
    UC_n A ↔ ∃ x : Fin n, 2 * freq A x ≥ A.length := by
  constructor
  · rintro ⟨x, hx⟩
    have h := freq_add_notFreq A x
    exact ⟨x, by omega⟩
  · rintro ⟨x, hx⟩
    have h := freq_add_notFreq A x
    exact ⟨x, by omega⟩

/-! ## The Doubling Construction `A = B ∪ { S ∪ {z} : S ∈ B }` -/

def liftBit {m : Nat} (bit : Bool) (S : Fin m → Bool) : Fin (m + 1) → Bool :=
  fun i => if h : i.val < m then S ⟨i.val, h⟩ else bit

def doubleFam {m : Nat} (B : List (Fin m → Bool)) : List (Fin (m + 1) → Bool) :=
  B.map (liftBit false) ++ B.map (liftBit true)

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

theorem doubleFam_isUnionClosed {m : Nat} (B : List (Fin m → Bool))
    (hB : isUnionClosed B) : isUnionClosed (doubleFam B) := by
  rcases hB with ⟨hne, hnd, huc, hcov⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- nonempty
    intro hnil
    have hlen : (doubleFam B).length = 0 := by rw [hnil]; rfl
    simp [doubleFam] at hlen
    exact hne hlen
  · -- Nodup
    apply nodup_append_disjoint
    · exact nodup_map_inj (liftBit false) (fun _ _ => liftBit_inj false) hnd
    · exact nodup_map_inj (liftBit true) (fun _ _ => liftBit_inj true) hnd
    · intro x hx1 hx2
      obtain ⟨S, _, rfl⟩ := List.mem_map.mp hx1
      obtain ⟨T, _, hEq⟩ := List.mem_map.mp hx2
      exact liftBit_false_ne_true S T hEq.symm
  · -- union-closed
    intro X hX Y hY
    have union_lift : ∀ (b1 b2 : Bool) (S T : Fin m → Bool),
        (fun i => liftBit b1 S i || liftBit b2 T i) =
        liftBit (b1 || b2) (fun j => S j || T j) := by
      intro b1 b2 S T
      funext i
      simp only [liftBit]
      split <;> rfl
    rcases List.mem_append.mp hX with hX0 | hX1 <;>
    rcases List.mem_append.mp hY with hY0 | hY1
    · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hX0
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hY0
      rw [union_lift]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_, huc S hS T hT, rfl⟩)
    · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hX0
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hY1
      rw [union_lift]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, huc S hS T hT, rfl⟩)
    · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hX1
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hY0
      rw [union_lift]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, huc S hS T hT, rfl⟩)
    · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hX1
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hY1
      rw [union_lift]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, huc S hS T hT, rfl⟩)
  · -- covers all of Fin (m + 1)
    intro i
    by_cases him : i.val < m
    · obtain ⟨S, hSB, hSi⟩ := hcov ⟨i.val, him⟩
      refine ⟨liftBit false S, List.mem_append_left _ (List.mem_map.mpr ⟨S, hSB, rfl⟩), ?_⟩
      simp [liftBit, him, hSi]
    · cases hB_eq : B with
      | nil => exact absurd hB_eq hne
      | cons S0 rest =>
        refine ⟨liftBit true S0, List.mem_append_right _ (List.mem_map.mpr ⟨S0, List.mem_cons_self .., rfl⟩), ?_⟩
        simp [liftBit, him]

theorem doubleFam_length {m : Nat} (B : List (Fin m → Bool)) :
    (doubleFam B).length = 2 * B.length := by
  simp [doubleFam]
  omega

theorem countP_map_const {α β : Type} (l : List α) (f : α → β) (p : β → Bool) (b : Bool)
    (h : ∀ x ∈ l, p (f x) = b) :
    (l.map f).countP p = if b then l.length else 0 := by
  induction l with
  | nil => cases b <;> simp
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    cases b <;> simp [ha, ht] <;> omega

theorem freq_doubleFam_last {m : Nat} (B : List (Fin m → Bool)) :
    freq (doubleFam B) (Fin.last m) = B.length := by
  simp only [freq, doubleFam, List.countP_append]
  have h0 : (B.map (liftBit false)).countP (fun S => S (Fin.last m)) = 0 := by
    simpa using countP_map_const B (liftBit false) (fun S => S (Fin.last m)) false
      (fun S _ => by simp [liftBit, Fin.last])
  have h1 : (B.map (liftBit true)).countP (fun S => S (Fin.last m)) = B.length := by
    simpa using countP_map_const B (liftBit true) (fun S => S (Fin.last m)) true
      (fun S _ => by simp [liftBit, Fin.last])
  rw [h0, h1]
  omega

theorem freq_doubleFam_lt {m : Nat} (B : List (Fin m → Bool)) (x : Fin (m + 1)) (hx : x.val < m) :
    freq (doubleFam B) x = 2 * freq B ⟨x.val, hx⟩ := by
  simp only [freq, doubleFam, List.countP_append, List.countP_map]
  have heq : ∀ (bit : Bool),
      B.countP ((fun S => S x) ∘ liftBit bit) = B.countP (fun S => S ⟨x.val, hx⟩) := by
    intro bit
    induction B with
    | nil => rfl
    | cons S t iht =>
      simp [List.countP_cons, Function.comp_def, liftBit, hx]
  rw [heq false, heq true]
  omega

theorem doubleFam_satisfies_UC_n {m : Nat} (B : List (Fin m → Bool)) :
    UC_n (doubleFam B) := by
  rw [UC_n_iff_half]
  refine ⟨Fin.last m, ?_⟩
  rw [freq_doubleFam_last, doubleFam_length]
  omega

/-! ## Main Theorem: `(∀ A, UC_n A → UC_{n-1} A) → Frankl's Conjecture` -/

/-- **Theorem (Bouchard Question 2.5 Equivalence):**
If an affirmative answer holds for Bouchard's Question 2.5 even at the single adjacent rung
`UC_n A → UC_{n-1} A` (for all finite union-closed families `A` on ground set `[n]` with `n ≥ 2`),
then Frankl's Union-Closed Sets Conjecture holds for every finite union-closed family `B`
on any nonempty ground set `[m]` (`m ≥ 1`). -/
theorem bouchard_q25_implies_frankl
    (hQ25 : ∀ (n : Nat), 2 ≤ n → ∀ (A : List (Fin n → Bool)),
      isUnionClosed A → UC_n A → UC_n_minus_1 A) :
    ∀ (m : Nat), 1 ≤ m → ∀ (B : List (Fin m → Bool)),
      isUnionClosed B → ∃ x : Fin m, 2 * freq B x ≥ B.length := by
  intro m hm B hB
  let A := doubleFam B
  have hA_uc : isUnionClosed A := doubleFam_isUnionClosed B hB
  have hA_UCn : UC_n A := doubleFam_satisfies_UC_n B
  have hn2 : 2 ≤ m + 1 := by omega
  obtain ⟨a, b, hab, hpair⟩ := hQ25 (m + 1) hn2 A hA_uc hA_UCn
  have hid := pair_identity A a b
  have hsum : freq A a + freq A b ≥ 2 * B.length := by
    have hlen : A.length = 2 * B.length := doubleFam_length B
    omega
  by_cases ha : a.val < m
  · by_cases hb : b.val < m
    · -- Both a, b ∈ V
      rw [freq_doubleFam_lt B a ha, freq_doubleFam_lt B b hb] at hsum
      by_cases hcmp : freq B ⟨a.val, ha⟩ ≥ freq B ⟨b.val, hb⟩
      · exact ⟨⟨a.val, ha⟩, by omega⟩
      · exact ⟨⟨b.val, hb⟩, by omega⟩
    · -- b = z = Fin.last m, a ∈ V
      have hbeq : b = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
      rw [hbeq, freq_doubleFam_lt B a ha, freq_doubleFam_last B] at hsum
      exact ⟨⟨a.val, ha⟩, by omega⟩
  · -- a = z = Fin.last m, so b ≠ a implies b.val < m
    have haeq : a = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
    by_cases hb : b.val < m
    · rw [haeq, freq_doubleFam_last B, freq_doubleFam_lt B b hb] at hsum
      exact ⟨⟨b.val, hb⟩, by omega⟩
    · have hbeq : b = Fin.last m := Fin.ext (by simp [Fin.last]; omega)
      exact absurd (haeq.trans hbeq.symm) hab

end BouchardQ25

#print axioms BouchardQ25.bouchard_q25_implies_frankl
