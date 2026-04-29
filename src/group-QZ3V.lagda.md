```
module group-QZ3V where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import UF.Sets

open import group-0000
open Group {{...}}
open import group-0004
```

因為等一下就會用到，首先證明如果 `G` 是群，那 `G × G` 是群

```
instance
  G×G-Group : {G : 𝓤 ̇} {{_ : Group G}} → Group (G × G)
  G×G-Group .size = ×-is-set size size
  G×G-Group ._∙_ (a , b) (a' , b') = a ∙ a' , b ∙ b'
  G×G-Group .∙-assoc (a , b) (a' , b') (a'' , b'') =
    a ∙ a' ∙ a'' , b ∙ b' ∙ b''   ＝⟨ ap (_, b ∙ b' ∙ b'') (∙-assoc a a' a'') ⟩
    a ∙ (a' ∙ a'') , b ∙ b' ∙ b'' ＝⟨ ap (a ∙ (a' ∙ a'') ,_) (∙-assoc b b' b'') ⟩
    a ∙ (a' ∙ a'') , b ∙ (b' ∙ b'') ∎
  G×G-Group .e = e , e
  G×G-Group .neu-l (a , b) =
    e ∙ a , e ∙ b ＝⟨ ap (_, e ∙ b) (neu-l a) ⟩
    a , e ∙ b     ＝⟨ ap (a ,_) (neu-l b) ⟩
    a , b ∎
  G×G-Group .neu-r (a , b) =
    a ∙ e , b ∙ e ＝⟨ ap (a ∙ e ,_) (neu-r b) ⟩
    a ∙ e , b     ＝⟨ ap (_, b) (neu-r a) ⟩
    a , b ∎
  G×G-Group ._⁻¹ (a , b) = a ⁻¹ , b ⁻¹
  G×G-Group .cancel {x} = I , II
    where
    I : (x .pr₁)⁻¹ ∙ (x .pr₁) , (x .pr₂)⁻¹ ∙ (x .pr₂) ＝ e , e
    I =
      (x .pr₁)⁻¹ ∙ (x .pr₁) , (x .pr₂)⁻¹ ∙ (x .pr₂) ＝⟨ ap (_, x .pr₂ ⁻¹ ∙ x .pr₂) (cancel .pr₁) ⟩
      e , (x .pr₂)⁻¹ ∙ (x .pr₂) ＝⟨ ap (e ,_) (cancel .pr₁) ⟩
      e , e ∎
    II : (x .pr₁) ∙ (x .pr₁)⁻¹ , (x .pr₂) ∙ (x .pr₂)⁻¹ ＝ e , e
    II =
      (x .pr₁) ∙ (x .pr₁)⁻¹ , (x .pr₂) ∙ (x .pr₂)⁻¹ ＝⟨ ap ((x .pr₁) ∙ (x .pr₁)⁻¹ ,_) (cancel .pr₂) ⟩
      (x .pr₁) ∙ (x .pr₁)⁻¹ , e ＝⟨ ap (_, e) (cancel .pr₂) ⟩
      e , e ∎
```

## Eckmann–Hilton argument

如果群的二元運算 `a ∙ b` 本身就是一個 group homomorphism，那麼 `G` 是交換群

```
mul-is-hom-leads-commutative : {G : 𝓤 ̇} {{∈G : Group G}}
  (μ : G × G → G)
  → ((a b : G) → μ(a , b) ＝ a ∙ b)
  → (μ-is-hom : IsGroupHomomorphism (G × G) G μ)
  → (x y : G) → x ∙ y ＝ y ∙ x
mul-is-hom-leads-commutative {𝓤} {G} {{_}} μ μ-is-mul μ-is-hom x y =
  x ∙ y               ＝⟨ ap (_∙ y) (sym (neu-l x)) ⟩
  (e ∙ x) ∙ y         ＝⟨ ap (e ∙ x ∙_) (sym (neu-r y)) ⟩
  (e ∙ x) ∙ (y ∙ e)   ＝⟨ sym (μ-is-mul (e ∙ x) (y ∙ e)) ⟩
  μ(e ∙ x , y ∙ e)    ＝⟨ interchange e y x e ⟩
  μ(e , y) ∙ μ(x , e) ＝⟨ ap (_∙ μ (x , e)) (μ-is-mul e y) ⟩
  (e ∙ y) ∙ μ(x , e)  ＝⟨ ap (_∙ μ (x , e)) (neu-l y) ⟩
  y ∙ μ(x , e)        ＝⟨ ap (y ∙_) (μ-is-mul x e) ⟩
  y ∙ (x ∙ e)         ＝⟨ ap (y ∙_) (neu-r x) ⟩
  y ∙ x ∎
  where
  interchange : (a b c d : G) → μ (a ∙ c , b ∙ d) ＝ μ (a , b) ∙ μ (c , d)
  interchange a b c d = μ-is-hom (a , b) (c , d)
```

反過來也很明顯，我們只需要證明交換會符合 interchange law

```
comm-leads-interchange : {G : 𝓤 ̇} {{∈G : Group G}}
  → ((x y : G) → x ∙ y ＝ y ∙ x)
  → ((a b c d : G) → (a ∙ c) ∙ (b ∙ d) ＝ (a ∙ b) ∙ (c ∙ d))
comm-leads-interchange comm a b c d =
  (a ∙ c) ∙ (b ∙ d) ＝⟨ ∙-assoc a c (b ∙ d) ⟩
  a ∙ (c ∙ (b ∙ d)) ＝⟨ ap (a ∙_) (sym (∙-assoc c b d)) ⟩
  a ∙ ((c ∙ b) ∙ d) ＝⟨ ap (a ∙_) (ap (_∙ d) (comm c b)) ⟩
  a ∙ ((b ∙ c) ∙ d) ＝⟨ ap (a ∙_) (∙-assoc b c d) ⟩
  a ∙ (b ∙ (c ∙ d)) ＝⟨ sym (∙-assoc a b (c ∙ d)) ⟩
  (a ∙ b) ∙ (c ∙ d) ∎
```
