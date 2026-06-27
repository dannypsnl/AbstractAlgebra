@title{Group Homomorphism}
@taxon{Definition}

@agda|{
module group-0004 where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)

open import group-0000
open Group {{...}}
}|

@p{我們先看 group homomorphism 的定義：}

@agda|{
IsGroupHomomorphism : (G H : 𝓤 ̇) {{_ : Group G}} {{_ : Group H}} → (φ : G → H) → 𝓤 ̇
IsGroupHomomorphism G H φ = (x y : G) → φ (x ∙ y) ＝ (φ x) ∙ (φ y)
}|

@p{基本上它的意思是，我們定義如果函數 @m{\varphi : G \to H} 能讓}

@mm{
\varphi(a \bullet b) = \varphi(a) \bullet \varphi(b)
}

@p{對所有 @m{a,b \in G} 成立，那 @m{\varphi} 是一個 group homomorphism。}

@p{這些 homomorphism 之所以特別，就是它們保留了一些結構，讓我們能夠對群整體做出推論，這種想法以範疇論為主，有非常多有趣又深刻的延伸。}
