@title{Preserve identity}
@taxon{Proposition}

@agda|{
module group-0005 where

open import MLTT.Spartan renaming (_⁻¹ to sym; _∙_ to _then_)

open import group-0000
open Group {{...}}
open import group-0003
open import group-0004
}|

@p{Group homomorphism 保留單位元素，也就是說 @m{\varphi(e_G) = e_H}。}

@blockquote{注意到雖然我們在數學式裡面用下標 @m{{}_G}、@m{{}_H} 區分，但在 Agda 裡面它自己就知道這件事，所以不用特別寫出}

@agda|{
proposition-4 : {G H : 𝓤 ̇} {{∈G : Group G}} {{∈H : Group H}}
  → (φ : G → H)
  → IsGroupHomomorphism G H φ
  → φ e ＝ e
proposition-4 φ is-hom = II
  where
}|

@p{證明 @m{\varphi(e_G) \bullet \varphi(e_G) = e_H \bullet \varphi(e_G)}}

@agda|{
  I : (φ e) ∙ (φ e) ＝ e ∙ (φ e)
  I = (φ e) ∙ (φ e) ＝⟨ sym (is-hom e e) ⟩
      φ (e ∙ e)     ＝⟨ ap φ (neu-l e)  ⟩
      φ e           ＝⟨ sym (neu-l (φ e)) ⟩
      e ∙ φ e ∎
}|

@p{那我們就可以用前面證明過的 @mention["group-0003"]{Proposition 3 任何元素都能取消} 得出結論}

@agda|{
  II : (φ e) ＝ e
  II = (proposition-3 .pr₁) I
}|
