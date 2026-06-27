@title{Normal subgroup equivalent condition}
@taxon{Proposition}

@agda|{
module group-000C where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)

open import group-0000
open Group {{...}}
open import group-0004
open import group-0006
}|

@blockquote{為了避免複雜的編碼，下面直接根據需求定義。}

@p{這個命題是說，任何 @m{\varphi : H → G} 的 Kernel 都是 @m{H} 的 normal subgroup。
所以我們想要證明的是對於任何屬於 Kernel 的元素 @m{h}，元素 @m{g \bullet h \bullet g^{-1}} 也屬於 Kernel。}

@p{前面已經提過 @m{\varphi} 的 Kernel 的定義是 @m{\varphi h = e} 的那些元素，因此定義 @code{x ∈Ker[ φ , φ-is-hom ]} 為 @code{φ x = e}。}

@agda|{
_∈Ker[_,_] : {H G : 𝓤 ̇} {{∈H : Group H}} {{∈G : Group G}} (h : H) → (φ : H → G) → IsGroupHomomorphism H G φ → 𝓤 ̇
h ∈Ker[ φ , is-hom ] = φ h ＝ e
}|

@blockquote{明確提供 @code{IsGroupHomomorphism} 是無奈之舉，因為以目前的定義方式，如果把 @code{IsGroupHomomorphism} 設為隱式參數，agda 會找不到而留下一個未解的變量。}

@agda|{
proposition-9 : {H G : 𝓤 ̇} {{∈H : Group H}} {{∈G : Group G}}
  (f : H → G) → (is-hom : IsGroupHomomorphism H G f)
  → ((h : H) → h ∈Ker[ f , is-hom ] → (g : H) → g ∙ h ∙ g ⁻¹ ∈Ker[ f , is-hom ])
proposition-9 {𝓤} {H}{G}{{∈H}}{{∈G}} f is-hom h in-ker g = I
  where
  I : f (g ∙ h ∙ g ⁻¹) ＝ e
  I = f (g ∙ h ∙ g ⁻¹)     ＝⟨ is-hom (g ∙ h) (g ⁻¹) ⟩
      f (g ∙ h) ∙ f (g ⁻¹) ＝⟨ ap (_∙ f (g ⁻¹)) (is-hom g h)  ⟩
      f g ∙ f h ∙ f (g ⁻¹) ＝⟨ ap (f g ∙ f h ∙_) (proposition-5 f is-hom g) ⟩
      f g ∙ f h ∙ f g ⁻¹   ＝⟨ ap (λ x → f g ∙ x ∙ f g ⁻¹) in-ker ⟩
}|

@p{因為 @code{h} 屬於 Kernel 所以 @code{f h} 可以換成 @code{e}}

@agda|{
      f g ∙ e ∙ f g ⁻¹     ＝⟨ ap (_∙ f g ⁻¹) (neu-r (f g)) ⟩
      f g ∙ f g ⁻¹         ＝⟨ cancel .pr₂ ⟩
      e ∎
}|
