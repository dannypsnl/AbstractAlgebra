```
module Group.HomBasic where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties

open import Group.Def
open Group {{...}}
open import Group.Basic
open import Group.DefHom
```

所以我們接著來看一個 group homomorphism 會有什麼特性。

## Proposition 4

Group homomorphism 保留單位元素，也就是說 $\varphi(e_G) = e_H$。

> 注意到雖然我們在數學式裡面用下標 $_G$、$_H$ 區分，但在 Agda 裡面它自己就知道這件事，所以不用特別寫出

```
proposition-4 : {G H : 𝓤 ̇} {{∈G : Group G}} {{∈H : Group H}}
  → (φ : G → H)
  → IsGroupHomomorphism G H φ
  → φ e ＝ e
proposition-4 φ is-hom = II
  where
```

證明 $\varphi(e_G) \bullet \varphi(e_G) = e_H \bullet \varphi(e_G)$

```
  I : (φ e) ∙ (φ e) ＝ e ∙ (φ e)
  I = (φ e) ∙ (φ e) ＝⟨ sym (is-hom e e) ⟩
      φ (e ∙ e)     ＝⟨ ap (λ x → φ x) (neu-l e)  ⟩
      φ e           ＝⟨ sym (neu-l (φ e)) ⟩
      e ∙ φ e ∎
```

那我們就可以用前面證明過的 [[Proposition 3] 任何元素都能取消](/Group.Basic/) 得出結論

```
  II : (φ e) ＝ e
  II = (proposition-3 .pr₁) I
```

## Proposition 5

Group homomorphism 保留反元素，也就是說 $\varphi(g^{-1}) = \varphi(g)^{-1}$ 對所有 $g \in G$ 成立。

```
proposition-5 : {G H : 𝓤 ̇} {{∈G : Group G}} {{∈H : Group H}}
  → (φ : G → H)
  → IsGroupHomomorphism G H φ
  → (g : G)
  → φ (g ⁻¹) ＝ (φ g) ⁻¹
proposition-5 φ is-hom g = (proposition-3 .pr₁) V
  where
  I : φ (g ⁻¹ ∙ g) ＝ φ (g ⁻¹) ∙ φ g
  I = is-hom (g ⁻¹) g
```

這裡馬上就用到剛剛證明的保留 identity 性質

```
  II : φ (g ⁻¹ ∙ g) ＝ e
  II = φ (g ⁻¹ ∙ g) ＝⟨ ap (λ x → φ x) (cancel .pr₁) ⟩
       φ e          ＝⟨ proposition-4 φ is-hom ⟩
       e ∎

  III : φ (g ⁻¹) ∙ φ g ＝ e
  III = (sym I) then II

  IV : (φ g) ⁻¹ ∙ (φ g) ＝ e
  IV = cancel .pr₁

  V : φ (g ⁻¹) ∙ φ g ＝ (φ g) ⁻¹ ∙ (φ g)
  V = III then (sym IV)
```
