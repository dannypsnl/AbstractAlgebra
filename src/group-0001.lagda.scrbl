@title{Identity is unique}
@taxon{Proposition}

@agda|{
module group-0001 where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)

open import group-0000
open Group {{...}}
}|

@p{假設元素 @m{h \in G} 是另一個滿足單位元素條件的元素，那 @m{h = e}。}

@blockquote{事實上，很酷的事情是甚至不用完全滿足單位元素條件，就如下面的證明所演示的}

@agda|{
proposition-1 : {G : 𝓤 ̇} {{_ : Group G}} {h : G} → left-neutral h _∙_ → h ＝ e
proposition-1 {G}{_} {h} h-is-identity =
  h     ＝⟨ sym (neu-r h) ⟩
  h ∙ e ＝⟨ h-is-identity e ⟩
  e ∎
}|

@p{這個命題的重點是單位元素是唯一的，所以英文的話你可以用「the」修飾。}

@blockquote{@code{sym} 把等式翻面：@code{A ＝ B} 變成 @code{B ＝ A}}
