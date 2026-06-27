@title{Trivial group is a subgroup of all groups}
@taxon{Proposition}

@agda|{
module group-0008 where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)
open import UF.Subsingletons
open import UF.Subsingletons-Properties

open import group-0000
open Group {{...}}
open import group-0004
open import group-0007
}|

@p{這個命題是說，對所有群都有一個子群是 trivial group。}

@p{要證明之前，我們需要看一下什麼是 trivial group，基本上它就是只有一個估拎拎的 @m{e} 元素的集合，那因為只有一個元素，能定義的二元運算子也就只有一個，根據這些我們可以定義 trivial group（@code{𝟙} 是一個只有單一元素 @code{⋆} 的型別）}

@agda|{
trivial-group : Group (𝟙 {𝓤})
trivial-group .size = props-are-sets 𝟙-is-prop
trivial-group ._∙_ = λ _ _ → ⋆
trivial-group .∙-assoc = λ _ _ _ → refl
trivial-group .e = ⋆
trivial-group .neu-l = λ _ → refl
trivial-group .neu-r = λ _ → refl
trivial-group ._⁻¹ = λ _ → ⋆
trivial-group .cancel = refl , refl
}|

@p{現在我們可以回到證明，因為 @code{IsSubgroup} 是一個 Sigma 類型，所以我們需要提出一個 map @m{\iota}，然後證明這個 map 是 inclusion 而且是 group homomorphism。}

@agda|{
proposition-6 : {G : 𝓤 ̇} {{∈G : Group G}} {{∈𝟙 : Group 𝟙}}
  → IsSubgroup 𝟙 G
proposition-6 {𝓤} {G} = ι , lc , is-hom
  where
}|

@p{這個 map 在數學上常被稱為 canonical map，用來指示「很明顯」會選這個的意思，這在不同數學領域都會有類似的 canonical 的用法，雖然那個「明顯」可能很不一樣。}

@agda|{
  ι : 𝟙 → G
  ι ⋆ = e
}|

@p{它的 inclusion 特性很明顯，甚至都不用到 @code{p}，因為只有一個元素}

@agda|{
  lc : left-cancellable ι
  lc p = refl
}|

@p{最後要滿足 group homomorphism，下面利用 @m{e} 攤開出我們需要的表達式}

@agda|{
  is-hom : IsGroupHomomorphism 𝟙 G ι
  is-hom ⋆ ⋆ =
    ι (⋆ ∙ ⋆) ＝⟨by-definition⟩
    e         ＝⟨ sym (neu-l e) ⟩
    e ∙ e     ＝⟨by-definition⟩
    (ι ⋆) ∙ (ι ⋆) ∎
}|
