```agda
open import UF.FunExt
module Group.IsCat (fe : Fun-Ext) where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import Categories.Category fe

open import group-0000
open Group {{...}}
```

最後我們就用範疇論的常見笑話：群也可以視為一個範疇作為群論的收尾

```
group-is-cat : (G : 𝓥 ̇ ) {{_ : Group G}} → precategory 𝓤 𝓥
group-is-cat {𝓥}{𝓤} G = make str axioms
  where
```

這個範疇只會有一個物件，所以型別是 `𝟙`

```
  ob = 𝟙
```

這個範疇的 hom-set 就是群 `G`

```
  hom : 𝟙 → 𝟙 → 𝓥 ̇
  hom ⋆ ⋆ = G
```

物件 $x$ 的 identity hom $id_x$ 由 `G` 的 identity element 提供

```
  idn : 𝟙 → G
  idn ⋆ = e
```

`⊚` 表示 hom 的組合，計算上由 `G` 的 operation 提供

```
  ⊚ : (A B C : 𝟙) → (f g : G) → G
  ⊚ ⋆ ⋆ ⋆ f g = f ∙ g
```

這些構成了範疇論需要的基本資料

```
  str : category-structure 𝓤 𝓥
  str = ob , hom , idn , ⊚
```

我們需要證明它滿足範疇論所有 hom 的性質

1. hom-set 是一個集合
2. $id_x$ 接 $f$ 等於 $f$
3. $f$ 接 $id_x$ 等於 $f$
4. associativity 的性質

這些都是直接繼承 `G` 自己的性質。

```
  axioms : precategory-axioms str
  axioms = (λ A B → size) , (λ A B → neu-l) , (λ A B → neu-r) , final
    where
    final : (A B C D : 𝟙) → (f g h : G) → ⊚ A B D f (⊚ B C D g h) ＝ ⊚ A C D (⊚ A B C f g) h
    final A B C D f g h =
      ⊚ A B D f (⊚ B C D g h) ＝⟨by-definition⟩
      f ∙ (g ∙ h)             ＝⟨ sym (∙-assoc f g h) ⟩
      (f ∙ g) ∙ h             ＝⟨by-definition⟩
      ⊚ A C D (⊚ A B C f g) h ∎
```
