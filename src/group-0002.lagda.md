```agda
module group-0002 where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)

open import group-0000
open Group {{...}}
```

如果 $h_1$ and $h_2$ 的反元素都是 $g$，那 $h_1 = h_2$。或者我們會說反元素是唯一的，跟上面的命題的意義類似。

```
proposition-2 : {G : 𝓤 ̇} {{_ : Group G}} {g h1 h2 : G} → (g ∙ h1 ＝ e) → (g ∙ h2 ＝ e) → h1 ＝ h2
proposition-2 {G}{_} {g}{h1}{h2} fact1 fact2 =
  h1              ＝⟨ sym (neu-l h1) ⟩
  e ∙ h1          ＝⟨ ap (_∙ h1) (sym (cancel .pr₁)) ⟩
  g ⁻¹ ∙ g ∙ h1   ＝⟨ ∙-assoc (g ⁻¹) g h1 ⟩
  g ⁻¹ ∙ (g ∙ h1) ＝⟨ ap (g ⁻¹ ∙_) fact1 ⟩
  g ⁻¹ ∙ e        ＝⟨ ap ((g ⁻¹) ∙_) (sym fact2) ⟩
  g ⁻¹ ∙ (g ∙ h2) ＝⟨ sym (∙-assoc (g ⁻¹) g h2) ⟩
  g ⁻¹ ∙ g ∙ h2   ＝⟨ ap (_∙ h2) (cancel .pr₁) ⟩
  e ∙ h2          ＝⟨ neu-l h2 ⟩
  h2 ∎
```

> `ap` 把等式裡的 expression 中沒有變化的部分抽出來用的，這樣才能操作其餘要改變的部分
