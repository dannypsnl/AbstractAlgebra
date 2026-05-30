```agda
module group-DCHP where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties
open import group-0000
open Group {{...}}
```

參考 [nLab heap](https://ncatlab.org/nlab/show/heap)

Heap presentation 用一個三元運算 `p`（標準模型讀作 `p x y z = (x ∙ y ⁻¹) ∙ z`），
完全沒有挑出單位元，所以它記得的資訊比 group 少一個 nullary 運算。

```
record Heap (A : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    size    : is-set A
    p       : A → A → A → A
    p-r     : ∀ x y → p x y y ＝ x
    p-l     : ∀ x y → p x x y ＝ y
    p-assoc : ∀ a b c d g → p (p a b c) d g ＝ p a b (p c d g)

open Heap
Group→Heap : {G : 𝓤 ̇ } → {{Group G}} → Heap G
Group→Heap {𝓤}{G} {{∈G}} .size = Group.size ∈G
Group→Heap {𝓤}{G} {{∈G}} .p x y z = (x ∙ y ⁻¹) ∙ z
Group→Heap {𝓤}{G} {{∈G}} .p-r x y =
  (x ∙ y ⁻¹) ∙ y ＝⟨ ∙-assoc x (y ⁻¹) y ⟩
  x ∙ (y ⁻¹ ∙ y) ＝⟨ ap (x ∙_) (cancel .pr₁) ⟩
  x ∙ e          ＝⟨ neu-r x ⟩
  x ∎
Group→Heap {𝓤}{G} {{∈G}} .p-l x y =
  (x ∙ x ⁻¹) ∙ y ＝⟨ ap (_∙ y) (cancel .pr₂) ⟩
  e ∙ y          ＝⟨ neu-l y ⟩
  y ∎
Group→Heap {𝓤}{G} {{∈G}} .p-assoc a b c d g =
  a ∙ b ⁻¹ ∙ c ∙ d ⁻¹ ∙ g     ＝⟨ ∙-assoc (a ∙ b ⁻¹ ∙ c) (d ⁻¹) g ⟩
  a ∙ b ⁻¹ ∙ c ∙ (d ⁻¹ ∙ g)   ＝⟨ ∙-assoc (a ∙ b ⁻¹) c (d ⁻¹ ∙ g) ⟩
  a ∙ b ⁻¹ ∙ (c ∙ (d ⁻¹ ∙ g)) ＝⟨ ap (λ w → a ∙ b ⁻¹ ∙ w) (sym (∙-assoc c (d ⁻¹) g)) ⟩
  a ∙ b ⁻¹ ∙ (c ∙ d ⁻¹ ∙ g) ∎
```

要把一個 Heap 變回 Group，必須額外指定一個 basepoint `e₀ : A`

```
Heap→Group : {A : 𝓤 ̇ } → A → Heap A → Group A
Heap→Group {𝓤} {A} e₀ H .size = Heap.size H
Heap→Group {𝓤} {A} e₀ H ._∙_ x y = p H x e₀ y
Heap→Group {𝓤} {A} e₀ H .∙-assoc x y z = p-assoc H x e₀ y e₀ z
Heap→Group {𝓤} {A} e₀ H .e = e₀
Heap→Group {𝓤} {A} e₀ H .neu-l x = p-l H e₀ x
Heap→Group {𝓤} {A} e₀ H .neu-r x = p-r H x e₀
Heap→Group {𝓤} {A} e₀ H ._⁻¹ = λ x → p H e₀ x e₀
Heap→Group {𝓤} {A} e₀ H .cancel {x} = invˡ x , invʳ x
  where
    invˡ : (x : A) → p H (p H e₀ x e₀) e₀ x ＝ e₀
    invˡ x =
      p H (p H e₀ x e₀) e₀ x  ＝⟨ p-assoc H e₀ x e₀ e₀ x ⟩
      p H e₀ x (p H e₀ e₀ x)  ＝⟨ ap (p H e₀ x) (p-l H e₀ x) ⟩
      p H e₀ x x              ＝⟨ p-r H e₀ x ⟩
      e₀ ∎
    invʳ : (x : A) → p H x e₀ (p H e₀ x e₀) ＝ e₀
    invʳ x =
      p H x e₀ (p H e₀ x e₀)  ＝⟨ sym (p-assoc H x e₀ e₀ x e₀) ⟩
      p H (p H x e₀ e₀) x e₀  ＝⟨ ap (λ w → p H w x e₀) (p-r H x e₀) ⟩
      p H x x e₀              ＝⟨ p-l H x e₀ ⟩
      e₀ ∎
```
