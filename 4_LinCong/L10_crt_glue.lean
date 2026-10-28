unfold ModEq at hm hn ⊢

obtain ⟨k1, hk1⟩ := hm
obtain ⟨k2, hk2⟩ := hn

have h_eq : m * k1 = n * k2
· rw [← hk1, ← hk2]

have hprod : m ∣ k2 * n
· use k1
  have hcomm : k2 * n = n * k2
  · ring
  rw [hcomm, ← h_eq]

have h_swap : IsGCD n m 1
· exact gcd_symm m n 1 h_coprime

have hk2div : m ∣ k2
· exact euclids_lemma k2 n m hprod h_swap

obtain ⟨t, ht⟩ := hk2div

use t
rw [hk2, ht]
ring
