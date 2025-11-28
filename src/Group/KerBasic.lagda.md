```
{-# OPTIONS --allow-unsolved-metas #-}
module Group.KerBasic where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import UF.Base
open import UF.Equiv

open import Group.Def
open Group {{...}}
open import Group.DefHom
open import Group.DefKer
open import Group.HomBasic
```

## Proposition 8

這個命題是說，如果 group homomorphism $i : H \to G$ 是 inclusion，那 Kernel 的元素其實只有單位元素 $e_H$。

```
proposition-8 : {H G : 𝓤 ̇} {{∈H : Group H}} {{∈G : Group G}}
  (i : H → G) → (is-hom : IsGroupHomomorphism H G i)
  → left-cancellable i
  → ((y : Ker H G i is-hom) → e ＝ y .pr₁)
proposition-8 {𝓤} {H}{G}{{∈H}}{{∈G}} i is-hom inclusion (h , p) = inclusion I
  where
  I : i e ＝ i h
  I = (proposition-4 i is-hom) then (sym p)
```

這也順便說明了，用 Propopsition 4 就已經知道 $\text{Ker}\ i$ 最少最少也有一個 $e_H$，因此任何 Kernel 都不是空集合。
事實上這還可以說成，這樣 Kernel 就會跟 `𝟙` 同構，因為只有一個元素，這也表示這時候 Kernel 是 trivial group。

```
proposition-8' : {H G : 𝓤 ̇} {{∈H : Group H}} {{∈G : Group G}}
  (i : H → G) → (is-hom : IsGroupHomomorphism H G i)
  → left-cancellable i
  → Ker H G i is-hom ≃ 𝟙 {𝓤}
proposition-8' {𝓤} {H}{G}{{∈H}}{{∈G}} i is-hom inclusion =
  ι , (ρ , λ x → refl) , ρ , final
  where
  ι : Ker H G i is-hom → 𝟙
  ι _ = ⋆
  P4 = proposition-4 i is-hom
  ρ : 𝟙 → Ker H G i is-hom
  ρ ⋆ = e , P4

  final : (x : Ker H G i is-hom) → ρ ⋆ ＝ x
  final (k , hk) =
    ρ ⋆    ＝⟨by-definition⟩
    e , P4 ＝⟨ to-Σ-＝ (I , size (transport (λ h → i h ＝ e) I P4) hk) ⟩
    k , hk ∎
    where
    I : e ＝ k
    I = inclusion (i e ＝⟨ P4 ⟩
                   e   ＝⟨ sym hk ⟩
                   i k ∎)
```
