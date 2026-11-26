# Formal Lean 4 Proofs Around Frankl's Union-Closed Sets Conjecture

Pure **Lean 4** (`v4.36.0`) formalizations of three short results on open problems surrounding **Frankl's Union-Closed Sets Conjecture (UCC)**.

- **Zero external dependencies** (pure Lean 4 core — no Mathlib needed)
- **Zero `sorry`**, **zero custom axioms**, **zero warnings**
- Independently verified with `lean --version` (`Lean 4.36.0`, exit code `0`)

---

## Verified Results

### 1. Affirmative Solution to Bouchard's Open Question 2.2 (`BouchardQ22.lean`)
- **Problem source:** Christopher Bouchard, *"Conjectures on union-closed families of sets"* ([arXiv:2310.02482v2](https://arxiv.org/abs/2310.02482), Question 2.2 & Proposition 2.3); also listed as open on GEWU ([math-orp-2370](https://magazine.gewu-lab.ai/en/problems/math-orp-2370), Sept 8, 2026).
- **Verified theorems:**
  - `BouchardQ22.intersection_witness_lemma`: If $C_1, \dots, C_m$ are (not necessarily distinct) subsets of a finite set $U$ with $m > |U|$, then there exists a nonempty index subset $I$ with $\bigl|\bigcap_{j \in I} C_j\bigr| = |I| - 1$.
  - `BouchardQ22.bouchard_question_2_2`: If $\mathcal{F}$ is a finite multiset of finite sets with $|\mathcal{F}| > \bigl|\bigcup \mathcal{F}\bigr| + 1$, then there exists a nonempty proper sub-multiset $\mathcal{F}' \subsetneq \mathcal{F}$ with $|\mathcal{F}| - |\mathcal{F}'| = \bigl|\bigcup \mathcal{F}'\bigr| + 1$.
- **Consequence:** Combined with Bouchard's Proposition 2.3, this unconditionally proves $\mathrm{UC}_x$ for all $x \in \bigl[\lfloor n/2 \rfloor + 1\bigr]$ (improving $\lceil n/3 \rceil + 1$).
- **Axioms used:** `[propext, Quot.sound]` *(completely constructive — does not even use `Classical.choice`!)*

### 2. Equivalence of Bouchard's Open Question 2.5 to Frankl's Conjecture (`BouchardQ25.lean`)
- **Problem source:** Christopher Bouchard ([arXiv:2310.02482v2](https://arxiv.org/abs/2310.02482), Question 2.5); GEWU ([math-orp-2370](https://magazine.gewu-lab.ai/en/problems/math-orp-2370)).
- **Verified theorem:**
  - `BouchardQ25.bouchard_q25_implies_frankl`: If every finite union-closed family $\mathcal{A}$ on ground set $[n]$ ($n \ge 2$) satisfies $\mathrm{UC}_n(\mathcal{A}) \implies \mathrm{UC}_{n-1}(\mathcal{A})$, then Frankl's Union-Closed Sets Conjecture holds for every finite nontrivial union-closed family.
- **Axioms used:** `[propext, Classical.choice, Quot.sound]`

### 3. Disproof of Marigo & Schipani's Conjectures 4.1–4.4 and Sharp Infimum-0 Theorem (`MarigoSchipani.lean`)
- **Problem source:** Francesco Marigo & Davide Schipani, *"Remarks on Frankl's conjecture"* ([arXiv:1603.01215](https://arxiv.org/abs/1603.01215), 2016, Conjectures 4.1–4.4 and fixed-$r$ strengthenings on p. 7).
- **Verified theorems:**
  - `MarigoSchipani.marigo_schipani_conj_4_1_to_4_4_false`: Explicit 10-element, 38-set reduced union-closed family ("Cube + Coatoms" $\mathcal{F}_{5,5}^{\mathrm{co}}$) refuting Conjectures 4.1, 4.2, 4.3, and 4.4 directly on the literal sums over all $38 \times 38$ ordered pairs ($2 \cdot 2545 = 5090 < 5130 = 38 \cdot 135$; $2545 < 2585$; $3 \cdot 2545 = 7635 < 7715$).
  - `MarigoSchipani.marigo_schipani_infimum_zero`: For every fixed integer $r \ge 1$ and every $M \ge 1$, there exists a reduced union-closed family $\mathcal{F}$ with
    $$M \cdot \left(2 \sum_{x \in S} |F_x|^{r+1}\right) \;<\; |\mathcal{F}| \cdot \sum_{x \in S} |F_x|^r,$$
    proving $\inf_{\mathcal{F} \text{ reduced UC}} \frac{2 \sum |F_x|^{r+1}}{|\mathcal{F}| \sum |F_x|^r} = 0$ for every fixed $r \ge 1$.
- **Axioms used:** `[propext, Classical.choice, Quot.sound]`

---

## Reproducing Locally

Install Lean 4 (`v4.36.0`) via [`elan`](https://github.com/leanprover/elan) and run:

```bash
lean BouchardQ22.lean
lean BouchardQ25.lean
lean MarigoSchipani.lean
```

Expected output (exit code `0`, zero warnings):
```text
'BouchardQ22.intersection_witness_lemma' depends on axioms: [propext, Quot.sound]
'BouchardQ22.bouchard_question_2_2' depends on axioms: [propext, Quot.sound]
'BouchardQ25.bouchard_q25_implies_frankl' depends on axioms: [propext, Classical.choice, Quot.sound]
'MarigoSchipani.marigo_schipani_conj_4_1_to_4_4_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'MarigoSchipani.marigo_schipani_infimum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Author & Transparency Note

**Eymen Utku Genç** (High school student, Turkey).  
*These arguments and their Lean 4 formalizations were developed and verified with the assistance of AI tools.*  
Feedback, independent checks, and pointers to any related prior literature are warmly welcome!
