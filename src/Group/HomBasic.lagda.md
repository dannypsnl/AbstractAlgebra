```
module Group.HomBasic where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to concat)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties

open import Group.Def
open Group {{...}}
open import Group.Basic
open import Group.DefHom
```

## Proposition 4

Group homomorphism preserves identity element.

```
propopsition-4 : {G H : 𝓤 ̇} {{∈G : Group G}} {{∈H : Group H}}
  → (φ : G → H)
  → IsGroupHomomorphism G H φ
  → φ e ＝ e
propopsition-4 φ is-hom = VI
  where
  I : e ⁻¹ ＝ e
  I = e ⁻¹ ＝⟨ sym (neu-r (e ⁻¹)) ⟩
      e ⁻¹ ∙ e ＝⟨ cancel .pr₁ ⟩
      e ∎

  II : φ e ＝ (φ e) ∙ (φ e)
  II = φ e ＝⟨ ap (λ x → φ x) (sym (cancel .pr₁)) ⟩
       φ (e ⁻¹ ∙ e) ＝⟨ ap (λ x → φ (x ∙ e)) I ⟩
       φ (e ∙ e) ＝⟨ is-hom e e ⟩
       (φ e) ∙ (φ e) ∎

  III : (φ e) ∙ (φ e) ＝ e ∙ (φ e)
  III = (φ e) ∙ (φ e) ＝⟨ sym II ⟩
        φ e ＝⟨ sym (neu-l (φ e)) ⟩
        e ∙ φ e ∎

  VI : (φ e) ＝ e
  VI = (propopsition-3 .pr₁) III
```

## Proposition 5

Group homomorphism preserves inverse.

```
propopsition-5 : {G H : 𝓤 ̇} {{∈G : Group G}} {{∈H : Group H}}
  → (φ : G → H)
  → IsGroupHomomorphism G H φ
  → (g : G)
  → φ (g ⁻¹) ＝ (φ g) ⁻¹
propopsition-5 φ is-hom g = (propopsition-3 .pr₁) V
  where
  I : φ (g ⁻¹ ∙ g) ＝ φ (g ⁻¹) ∙ φ g
  I = is-hom (g ⁻¹) g

  II : φ (g ⁻¹ ∙ g) ＝ e
  II = φ (g ⁻¹ ∙ g) ＝⟨ ap (λ x → φ x) (cancel .pr₁) ⟩
       φ e ＝⟨ propopsition-4 φ is-hom ⟩
       e ∎

  III : φ (g ⁻¹) ∙ φ g ＝ e
  III = concat (sym I) II

  VI : (φ g) ⁻¹ ∙ (φ g) ＝ e
  VI = cancel .pr₁

  V : φ (g ⁻¹) ∙ φ g ＝ (φ g) ⁻¹ ∙ (φ g)
  V = concat III (sym VI)
```
