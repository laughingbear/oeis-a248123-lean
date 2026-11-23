import Mathlib
import PrimeNumberTheoremAnd.Consequences

/-!
# OEIS A248123: a(n) exists for every n > 0

`a(n)` is the least `m > 0` with `gcd(m, n) = 1` and `m * n ∣ C(m + n)`, where `C` is the Catalan
number. Zhi-Wei Sun conjectured (2014) that `a(n)` exists for all `n > 0`. This file proves it,
following the argument of Zedan Soorya (OEIS A248123, Nov 13 2026), with a simplified choice of
residues:

* `N = r * u + n` with primes `2n + 1 < u < r`, `3u ≤ 2r`, `r < 2u`;
* `N ≡ -2` modulo the square of the odd part of `n`, and `N ≡ -3` modulo `4` times the `2`-part
  of `n` (when `n` is even).

Kummer's theorem then gives `n`, `r` and `u` dividing `C(N)`. The prime `u` comes from Dirichlet's
theorem (Mathlib) and the prime `r` from the prime number theorem in arithmetic progressions
(`chebyshev_asymptotic_pnt` in PrimeNumberTheoremAnd).
-/

namespace A248123

open Nat Finset

/-- If `S` is a set of carry positions for `N + N` in base `p` that is large enough, then
`p ^ k ∣ catalan N`. -/
lemma pow_dvd_catalan_of_carries {p N k : ℕ} [hp : Fact p.Prime] (S : Finset ℕ)
    (hS : ∀ i ∈ S, 1 ≤ i ∧ p ^ i ≤ 2 * (N % p ^ i))
    (hcard : k + padicValNat p (N + 1) ≤ S.card) : p ^ k ∣ catalan N := by
  have hp1 : 1 < p := hp.out.one_lt
  have hb : Nat.log p (2 * N) < Nat.log p (2 * N) + 1 := Nat.lt_succ_self _
  have hkummer := padicValNat_choose (p := p) (n := 2 * N) (k := N) (by omega) hb
  have hsub : S ⊆ (Finset.Ico 1 (Nat.log p (2 * N) + 1)).filter
      (fun i => p ^ i ≤ N % p ^ i + (2 * N - N) % p ^ i) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hS i hi
    have hle : p ^ i ≤ 2 * N := le_trans h2 (by have := Nat.mod_le N (p ^ i); omega)
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨h1, Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp1 hle)⟩, ?_⟩
    rw [show 2 * N - N = N by omega]
    omega
  have hcb : padicValNat p (centralBinom N) ≥ S.card := by
    rw [centralBinom_eq_two_mul_choose, hkummer]
    exact Finset.card_le_card hsub
  have hcat0 : catalan N ≠ 0 := by
    have := succ_mul_catalan_eq_centralBinom N
    intro h; rw [h, mul_zero] at this; exact (centralBinom_ne_zero N) this.symm
  have hmul : padicValNat p (N + 1) + padicValNat p (catalan N) =
      padicValNat p (centralBinom N) := by
    rw [← succ_mul_catalan_eq_centralBinom, padicValNat.mul (by omega) hcat0]
  have hk : k ≤ padicValNat p (catalan N) := by omega
  exact (pow_dvd_pow p hk).trans pow_padicValNat_dvd

/-- `(Y - c) % X = X - c` when `X ∣ Y`, `0 < Y` and `1 ≤ c ≤ X`. -/
lemma sub_mod_of_dvd {X Y c : ℕ} (hXY : X ∣ Y) (hY : 0 < Y) (hc : 1 ≤ c) (hcX : c ≤ X) :
    (Y - c) % X = X - c := by
  obtain ⟨t, rfl⟩ := hXY
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · simp [h] at hY
    · exact h
  have : X * t - c = (X - c) + X * (t - 1) := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [Nat.mul_succ]; simp; omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Odd prime powers: if `N ≡ -2 (mod q ^ (e + 1))` then `q ^ e ∣ catalan N`. -/
lemma pow_dvd_catalan_odd {q e N : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hN : N % q ^ (e + 1) = q ^ (e + 1) - 2) : q ^ e ∣ catalan N := by
  have hq3 : 3 ≤ q := by
    have := hq.out.two_le; rcases Nat.lt_or_ge q 3 with h | h
    · exact absurd (by omega : q = 2) hq2
    · exact h
  have hmodi : ∀ i, i ≤ e + 1 → 1 ≤ i → N % q ^ i = q ^ i - 2 := by
    intro i hi hi1
    have hdvd : q ^ i ∣ q ^ (e + 1) := pow_dvd_pow q hi
    rw [← Nat.mod_mod_of_dvd N hdvd, hN]
    have : 2 ≤ q ^ i := le_trans (by omega) (Nat.le_self_pow (by omega) q)
    exact sub_mod_of_dvd hdvd (by positivity) (by norm_num) this
  apply pow_dvd_catalan_of_carries (Finset.Icc 2 (e + 1))
  · intro i hi
    rw [Finset.mem_Icc] at hi
    refine ⟨by omega, ?_⟩
    rw [hmodi i hi.2 (by omega)]
    have h9 : 9 ≤ q ^ i := le_trans (by nlinarith) (Nat.pow_le_pow_right (by omega) hi.1)
    omega
  · have h1 := hmodi 1 (by omega) le_rfl
    rw [pow_one] at h1
    have hN1 : (N + 1) % q = q - 1 := by
      rw [Nat.add_mod, h1, Nat.one_mod_eq_one.mpr (by omega), show q - 2 + 1 = q - 1 by omega,
        Nat.mod_eq_of_lt (by omega)]
    have hv : padicValNat q (N + 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega)
    simp [hv]

/-- Powers of two: if `N ≡ -3 (mod 2 ^ (e + 2))` then `2 ^ e ∣ catalan N`. -/
lemma pow_dvd_catalan_two {e N : ℕ} (hN : N % 2 ^ (e + 2) = 2 ^ (e + 2) - 3) :
    2 ^ e ∣ catalan N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodi : ∀ i, i ≤ e + 2 → 2 ≤ i → N % 2 ^ i = 2 ^ i - 3 := by
    intro i hi hi2
    have hdvd : 2 ^ i ∣ 2 ^ (e + 2) := pow_dvd_pow 2 hi
    rw [← Nat.mod_mod_of_dvd N hdvd, hN]
    have : 4 ≤ 2 ^ i := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hi2)
    exact sub_mod_of_dvd hdvd (by positivity) (by norm_num) (by omega)
  have h4 := hmodi 2 (by omega) le_rfl
  apply pow_dvd_catalan_of_carries (insert 1 (Finset.Icc 3 (e + 2)))
  · intro i hi
    rw [Finset.mem_insert, Finset.mem_Icc] at hi
    rcases hi with rfl | hi
    · refine ⟨le_rfl, ?_⟩
      have : N % 2 = 1 := by
        rw [← Nat.mod_mod_of_dvd N (show 2 ∣ 2 ^ 2 by norm_num), h4]; norm_num
      omega
    · refine ⟨by omega, ?_⟩
      rw [hmodi i hi.2 (by omega)]
      have : 8 ≤ 2 ^ i := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hi.1)
      omega
  · have hv : padicValNat 2 (N + 1) ≤ 1 := by
      by_contra hc
      have h4d : 2 ^ 2 ∣ N + 1 := (padicValNat_dvd_iff_le (p := 2) (by omega)).mpr (by omega)
      have : (N + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using h4d)
      have : N % 4 = 1 := by simpa using h4
      omega
    rw [Finset.card_insert_of_notMem (by simp)]
    simp only [Nat.card_Icc]
    omega

/-- One carry in the second digit: if `N % p ^ 2 = d * p + n` with `p ≤ 2 d` and `n + 1 < p`,
then `p ∣ catalan N`. -/
lemma dvd_catalan_of_digit {p d n N : ℕ} [hp : Fact p.Prime]
    (hN : N % p ^ 2 = d * p + n) (hd : p ≤ 2 * d) (hn : n + 1 < p) : p ∣ catalan N := by
  have h := pow_dvd_catalan_of_carries (p := p) (N := N) (k := 1) {2} ?_ ?_
  · simpa using h
  · intro i hi
    rw [Finset.mem_singleton] at hi; subst hi
    refine ⟨by norm_num, ?_⟩
    rw [hN]; nlinarith
  · have hp1 := hp.out.one_lt
    have hmodp : N % p = n := by
      rw [← Nat.mod_mod_of_dvd N (show p ∣ p ^ 2 from dvd_pow_self p two_ne_zero), hN,
        mul_comm d p, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hN1 : (N + 1) % p = n + 1 := by
      rw [Nat.add_mod, hmodp, Nat.one_mod_eq_one.mpr (by omega), Nat.mod_eq_of_lt hn]
    have hv : padicValNat p (N + 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega)
    simp [hv]


/-- Primes in a residue class in the interval `[3x/2, 2x)` for all large `x`. This follows from
the prime number theorem for arithmetic progressions. -/
def PrimesInAPInterval : Prop :=
  ∀ L c : ℕ, 0 < L → Nat.Coprime c L → ∃ X : ℕ, ∀ x ≥ X,
    ∃ p, p.Prime ∧ p ≡ c [MOD L] ∧ 3 * x ≤ 2 * p ∧ p < 2 * x

/-- `n ∣ catalan N` when `N ≡ -2` modulo the square of the odd part of `n`, and (if `n` is even)
`N ≡ -3` modulo `4` times the `2`-part of `n`. -/
lemma dvd_catalan_of_residues {n N : ℕ} (hn : 0 < n)
    (hA : N % (ordCompl[2] n) ^ 2 = ((ordCompl[2] n) ^ 2 - 2) % (ordCompl[2] n) ^ 2)
    (hB : 0 < n.factorization 2 →
      N % 2 ^ (n.factorization 2 + 2) = 2 ^ (n.factorization 2 + 2) - 3) :
    n ∣ catalan N := by
  set O := ordCompl[2] n with hO
  have hO0 : 0 < O := Nat.ordCompl_pos 2 hn.ne'
  have hOodd : ¬ 2 ∣ O := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
  have hcat0 : catalan N ≠ 0 := by
    have := succ_mul_catalan_eq_centralBinom N
    intro h; rw [h, mul_zero] at this; exact (centralBinom_ne_zero N) this.symm
  rw [← Nat.factorization_prime_le_iff_dvd hn.ne' hcat0]
  intro q hq
  have : Fact q.Prime := ⟨hq⟩
  by_cases hq2 : q = 2
  · subst hq2
    rcases Nat.eq_zero_or_pos (n.factorization 2) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · exact (hq.pow_dvd_iff_le_factorization hcat0).mp (pow_dvd_catalan_two (hB hpos))
  · set e := n.factorization q with he
    rcases Nat.eq_zero_or_pos e with h0 | hepos
    · rw [h0]; exact Nat.zero_le _
    have heO : O.factorization q = e := by
      rw [hO, Nat.factorization_ordCompl, Finsupp.erase_ne hq2]
    have hqeO : q ^ e ∣ O := by
      rw [← heO]; exact Nat.ordProj_dvd O q
    have hdvdA : q ^ (e + 1) ∣ O ^ 2 := by
      have : q ^ (e + 1) ∣ q ^ (2 * e) := pow_dvd_pow q (by omega)
      exact this.trans (by rw [pow_mul']; exact pow_dvd_pow_of_dvd hqeO 2)
    have h2le : 2 ≤ q ^ (e + 1) := le_trans hq.two_le (Nat.le_self_pow (by omega) q)
    have hNq : N % q ^ (e + 1) = q ^ (e + 1) - 2 := by
      rw [← Nat.mod_mod_of_dvd N hdvdA, hA, Nat.mod_mod_of_dvd _ hdvdA]
      exact sub_mod_of_dvd hdvdA (by positivity) (by norm_num) h2le
    exact (hq.pow_dvd_iff_le_factorization hcat0).mp (pow_dvd_catalan_odd hq2 hNq)

/-- **A248123**, assuming primes in residue classes in `[3x/2, 2x)`: for every `n > 0` there is
`m > 0` with `gcd(m, n) = 1` and `m n ∣ C(m + n)`. -/
theorem exists_m (hPNT : PrimesInAPInterval) (n : ℕ) (hn : 0 < n) :
    ∃ m, 0 < m ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n) := by
  set s := n.factorization 2 with hs
  set O := ordCompl[2] n with hO
  have hO0 : 0 < O := Nat.ordCompl_pos 2 hn.ne'
  have hOodd : ¬ 2 ∣ O := Nat.not_dvd_ordCompl Nat.prime_two hn.ne'
  set A := O ^ 2 with hA
  set B := if s = 0 then 1 else 2 ^ (s + 2) with hB
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < B := by rw [hB]; split_ifs <;> positivity
  have hAodd : ¬ 2 ∣ A := fun h => hOodd (Nat.prime_two.dvd_of_dvd_pow h)
  have hcop : Nat.Coprime A B := by
    rw [hB]; split_ifs
    · exact Nat.coprime_one_right _
    · exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hAodd).symm
  obtain ⟨N0, hN0A, hN0B⟩ := Nat.chineseRemainder hcop (A - 2) (B - 3)
  set L := A * B with hL
  have hL0 : 0 < L := Nat.mul_pos hA0 hB0
  set c := (N0 + L * n - n) % L with hc
  have hcn : c + n ≡ N0 [MOD L] := by
    have h1 : c ≡ N0 + L * n - n [MOD L] := Nat.mod_modEq _ _
    have h2 : c + n ≡ N0 + L * n - n + n [MOD L] := Nat.ModEq.add_right n h1
    rw [show N0 + L * n - n + n = N0 + L * n by
      have : n ≤ L * n := Nat.le_mul_of_pos_left n hL0
      omega] at h2
    exact h2.trans (by simp [Nat.ModEq, Nat.add_mul_mod_self_left])
  -- `c` is a unit modulo `L`
  have hcL : Nat.Coprime c L := by
    apply Nat.coprime_of_dvd
    intro k hk hkc hkL
    have hk2 : 2 ≤ k := hk.two_le
    have hN0k : N0 % k = 0 := by
      have hkn : k ∣ n ∨ True := Or.inr trivial
      rcases (Nat.Prime.dvd_mul hk).mp hkL with hkA | hkB
      · have hkO : k ∣ O := hk.dvd_of_dvd_pow hkA
        have hkn : k ∣ n := hkO.trans (Nat.ordCompl_dvd n 2)
        have := (Nat.ModEq.of_dvd hkL hcn).symm
        rw [Nat.ModEq] at this
        rw [this]; exact Nat.mod_eq_zero_of_dvd (dvd_add hkc hkn)
      · have hs0 : s ≠ 0 := by
          intro h0; rw [hB, ite_eq_left h0] at hkB; exact hk.one_lt.ne' (Nat.dvd_one.mp hkB)
        have hk2' : k = 2 := by
          rw [hB, ite_eq_right hs0] at hkB; exact (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).mp
            (hk.dvd_of_dvd_pow hkB)
        subst hk2'
        have hkn : 2 ∣ n := by
          have := Nat.ordProj_dvd n 2
          exact (dvd_pow_self 2 hs0).trans this
        have := (Nat.ModEq.of_dvd hkL hcn).symm
        rw [Nat.ModEq] at this
        rw [this]; exact Nat.mod_eq_zero_of_dvd (dvd_add hkc hkn)
    rcases (Nat.Prime.dvd_mul hk).mp hkL with hkA | hkB
    · have hkodd : k ≠ 2 := fun h => hAodd (h ▸ hkA)
      have h := (Nat.ModEq.of_dvd hkA hN0A)
      rw [Nat.ModEq, hN0k, sub_mod_of_dvd hkA hA0 (by norm_num) hk2] at h
      have : 3 ≤ k := by omega
      omega
    · have hs0 : s ≠ 0 := by
        intro h0; rw [hB, ite_eq_left h0] at hkB; exact hk.one_lt.ne' (Nat.dvd_one.mp hkB)
      have hk2' : k = 2 := by
        rw [hB, ite_eq_right hs0] at hkB; exact (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).mp
          (hk.dvd_of_dvd_pow hkB)
      subst hk2'
      have h := (Nat.ModEq.of_dvd hkB hN0B)
      rw [hB, ite_eq_right hs0] at h
      rw [Nat.ModEq, hN0k] at h
      have : (2 ^ (s + 2) - 3) % 2 = 1 := by
        have : 4 ≤ 2 ^ (s + 2) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (s + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ∣ 2 ^ (s + 2) := dvd_pow_self 2 (by omega)
        obtain ⟨t, ht⟩ := h2
        rw [ht]; omega
      omega
  -- the primes
  obtain ⟨X, hX⟩ := hPNT L c hL0 hcL
  obtain ⟨u, hu_gt, hu, hu1⟩ := Nat.forall_exists_prime_gt_and_modEq (X + 2 * n + 2)
    hL0.ne' (Nat.coprime_one_left L)
  obtain ⟨r, hr, hrc, hr1, hr2⟩ := hX u (by omega)
  have hru : u < r := by omega
  set N := r * u + n with hN
  have hNmod : N ≡ N0 [MOD L] := by
    have : r * u + n ≡ c * 1 + n [MOD L] := Nat.ModEq.add_right n (Nat.ModEq.mul hrc hu1)
    rw [mul_one] at this; exact this.trans hcn
  -- `n ∣ catalan N`
  have hndvd : n ∣ catalan N := by
    apply dvd_catalan_of_residues hn
    · have h := (Nat.ModEq.of_mul_right B hNmod).trans hN0A
      exact h
    · intro hpos
      have hs0 : s ≠ 0 := by omega
      have h := (Nat.ModEq.of_mul_left A hNmod).trans hN0B
      rw [hB, ite_eq_right hs0] at h
      rw [show n.factorization 2 = s from rfl, h]
      have h2 : 2 ∣ 2 ^ (s + 2) := dvd_pow_self 2 (by omega)
      have : 4 ≤ 2 ^ (s + 2) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (s + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact Nat.mod_eq_of_lt (by omega)
  -- `r ∣ catalan N`
  have : Fact r.Prime := ⟨hr⟩
  have : Fact u.Prime := ⟨hu⟩
  have hrdvd : r ∣ catalan N := by
    have hlt : N < r ^ 2 := by
      rw [hN, sq]; nlinarith
    apply dvd_catalan_of_digit (d := u) (n := n)
    · rw [Nat.mod_eq_of_lt hlt, hN, mul_comm]
    · omega
    · omega
  -- `u ∣ catalan N`
  have hudvd : u ∣ catalan N := by
    obtain ⟨d, hd⟩ : ∃ d, r = u + d := ⟨r - u, by omega⟩
    have hNu : N = (d * u + n) + u ^ 2 * 1 := by rw [hN, hd]; ring
    have hlt : d * u + n < u ^ 2 := by rw [sq]; nlinarith
    apply dvd_catalan_of_digit (d := d) (n := n)
    · rw [hNu, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    · omega
    · omega
  refine ⟨r * u, Nat.mul_pos hr.pos hu.pos, ?_, ?_⟩
  · have hrn : Nat.Coprime r n := (Nat.Prime.coprime_iff_not_dvd hr).mpr
      (fun h => by have := Nat.le_of_dvd hn h; omega)
    have hun : Nat.Coprime u n := (Nat.Prime.coprime_iff_not_dvd hu).mpr
      (fun h => by have := Nat.le_of_dvd hn h; omega)
    exact Nat.Coprime.mul_left hrn hun
  · have hrn : Nat.Coprime r n := (Nat.Prime.coprime_iff_not_dvd hr).mpr
      (fun h => by have := Nat.le_of_dvd hn h; omega)
    have hun : Nat.Coprime u n := (Nat.Prime.coprime_iff_not_dvd hu).mpr
      (fun h => by have := Nat.le_of_dvd hn h; omega)
    have hruc : Nat.Coprime r u := (Nat.coprime_primes hr hu).mpr (by omega)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.mul_left hrn hun)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd hruc hrdvd hudvd) hndvd


open Filter Asymptotics in
/-- The prime number theorem for arithmetic progressions, in the form proved as
`chebyshev_asymptotic_pnt` in PrimeNumberTheoremAnd. -/
def PNTinAP : Prop :=
  ∀ (q a : ℕ), q ≥ 1 → a.Coprime q → a < q →
    (fun x : ℝ ↦ ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊),
      if p % q = a then Real.log p else 0) ~[atTop] fun x ↦ x / q.totient

open Filter Asymptotics in
lemma primesInAPInterval_of_pnt (hPNT : PNTinAP) : PrimesInAPInterval := by
  intro L c hL hc
  set a := c % L with ha_def
  have ha : a.Coprime L := by
    show Nat.gcd (c % L) L = 1
    rw [← Nat.gcd_rec]; exact Nat.Coprime.symm hc
  have haL : a < L := Nat.mod_lt _ hL
  set θ : ℕ → ℝ := fun y ↦ ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic y),
    if p % L = a then Real.log p else 0 with hθ
  have hE := hPNT L a hL ha haL
  have hφ : (0 : ℝ) < L.totient := by exact_mod_cast Nat.totient_pos.mpr hL
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (hE.isLittleO.def (c := 1 / 10) (by norm_num))
  have hYn : ∀ y : ℕ, Y ≤ y →
      |θ y - y / L.totient| ≤ 1 / 10 * (y / L.totient) := by
    intro y hy
    have := hY y hy
    simp only [Pi.sub_apply, Real.norm_eq_abs, Nat.floor_natCast] at this
    rwa [abs_of_nonneg (div_nonneg (Nat.cast_nonneg y) hφ.le)] at this
  refine ⟨⌈Y⌉₊ + 3, fun x hx => ?_⟩
  have hxY : Y ≤ x := le_trans (Nat.le_ceil Y) (by exact_mod_cast (by omega : ⌈Y⌉₊ ≤ x))
  set y1 := 2 * x - 1 with hy1
  set y0 := (3 * x - 1) / 2 with hy0
  have hy01 : y0 ≤ y1 := by omega
  have hxy0 : x ≤ y0 := by omega
  have h1 := hYn y1 (le_trans hxY (by exact_mod_cast (by omega : x ≤ y1)))
  have h0 := hYn y0 (le_trans hxY (by exact_mod_cast hxy0))
  have hy1r : (y1 : ℝ) = 2 * x - 1 := by
    rw [hy1, Nat.cast_sub (by omega)]; push_cast; ring
  have hy0r : 2 * (y0 : ℝ) ≤ 3 * x - 1 := by
    have : 2 * y0 ≤ 3 * x - 1 := by omega
    have h3 : ((3 * x - 1 : ℕ) : ℝ) = 3 * x - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← h3]; exact_mod_cast this
  have hx3 : (3 : ℝ) ≤ x := by exact_mod_cast (by omega : 3 ≤ x)
  have hgt : θ y0 < θ y1 := by
    rw [abs_le] at h1 h0
    have key : (y0 : ℝ) / L.totient * (11 / 10) < (y1 : ℝ) / L.totient * (9 / 10) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right hφ]
      nlinarith
    linarith [h1.1, h0.2]
  by_contra hne
  push Not at hne
  have heq : θ y0 = θ y1 := by
    apply Finset.sum_subset
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Iic] at hp ⊢
      exact ⟨le_trans hp.1 hy01, hp.2⟩
    · intro p hp hp0
      simp only [Finset.mem_filter, Finset.mem_Iic, not_and] at hp hp0
      have hpy0 : y0 < p := by
        by_contra h; exact hp0 (by omega) hp.2
      rw [ite_eq_right]
      intro hpa
      have h2 := hne p hp.2 hpa (by omega)
      omega
  exact absurd heq hgt.ne

theorem exists_m_of_pnt (hPNT : PNTinAP) (n : ℕ) (hn : 0 < n) :
    ∃ m, 0 < m ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n) :=
  exists_m (primesInAPInterval_of_pnt hPNT) n hn

/-- The definition of `a` in `FormalConjectures/OEIS/248123.lean`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n) }

theorem conjecture_of_pnt (hPNT : PNTinAP) (n : ℕ) (hn : 0 < n) : 0 < a n := by
  obtain ⟨m, hm⟩ := exists_m_of_pnt hPNT n hn
  have hne : ({ m : ℕ | 0 < m ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n) } : Set ℕ).Nonempty :=
    ⟨m, hm⟩
  exact (Nat.sInf_mem hne).1

/-- **OEIS A248123** (the statement `OeisA248123.conjecture` of Formal Conjectures):
`a(n)` exists for all `n > 0`. -/
theorem conjecture (n : ℕ) (hn : 0 < n) : 0 < a n :=
  conjecture_of_pnt (fun _ _ hq ha ha' => chebyshev_asymptotic_pnt hq ha ha') n hn

end A248123
