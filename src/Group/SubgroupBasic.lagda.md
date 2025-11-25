```
module Group.SubgroupBasic where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to concat)
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-Properties

open import Group.Def
open Group {{...}}
open import Group.DefHom
open import Group.HomBasic
open import Group.DefSubgroup
```

## Propopsition 6

這個命題是說，對所有群都有一個子群是 trivial group。

要證明之前，我們需要看一下什麼是 trivial group，基本上它就是只有一個估拎拎的 $e$ 元素的集合，那因為只有一個元素，能定義的二元運算子也就只有一個，根據這些我們可以定義 trivial group（`𝟙` 是一個只有單一元素 `⋆` 的型別）

```
trivial-group : Group (𝟙 {𝓤})
trivial-group = record
  { size = props-are-sets 𝟙-is-prop
  ; _∙_ = λ _ _ → ⋆
  ; ∙-assoc = λ _ _ _ → refl
  ; e = ⋆
  ; neu-l = λ _ → refl
  ; neu-r = λ _ → refl
  ; _⁻¹ = λ _ → ⋆
  ; cancel = λ {_} → refl , refl
  }
```

現在我們可以回到證明，因為 `IsSubgroup` 是一個 Sigma 類型，所以我們需要提出一個 map $\iota$，然後證明這個 map 是 inclusion 而且是 group homomorphism。

```
propopsition-6 : {G : 𝓤 ̇} {{∈G : Group G}} {{∈𝟙 : Group 𝟙}}
  → IsSubgroup 𝟙 G
propopsition-6 {𝓤} {G} = ι , lc , is-hom
  where
```

這個 map 在數學上常被稱為 canonical map，用來指示「很明顯」會選這個的意思，這在不同數學領域都會有類似的 canonical 的用法，雖然那個「明顯」可能很不一樣。

```
  ι : 𝟙 → G
  ι ⋆ = e
```

它的 inclusion 特性很明顯，甚至都不用到 `p`，因為只有一個元素

```
  lc : left-cancellable ι
  lc p = refl
```

比較複雜的會是滿足 group homomorphism 的部分，大致的思考是利用 $e$ 的一些特性攤開出我們需要的表達式

```
  is-hom : IsGroupHomomorphism 𝟙 G ι
  is-hom ⋆ ⋆ =
    ι (⋆ ∙ ⋆) ＝⟨ refl ⟩
    e ＝⟨ sym (cancel .pr₁) ⟩
    (ι ⋆)⁻¹ ∙ (ι ⋆) ＝⟨ refl ⟩
    e ⁻¹ ∙ (ι ⋆) ＝⟨ ap (_∙ (ι ⋆)) (concat ((sym (neu-r (e ⁻¹)))) (cancel .pr₁)) ⟩
    e ∙ (ι ⋆) ＝⟨ refl ⟩
    (ι ⋆) ∙ (ι ⋆) ∎
```
