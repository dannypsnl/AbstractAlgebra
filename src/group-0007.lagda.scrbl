@title{子群 Subgroup}
@taxon{Definition}

@agda|{
module group-0007 where

open import MLTT.Spartan

open import group-0000
open import group-0004
}|

@p{子群的定義是，如果存在一個 inclusion 函數 @m{i : H \to G} 是一個 group homomorphism，那 @m{H} 是 @m{G} 的子群。}

@agda|{
IsSubgroup : {𝓤 : Universe} (H G : 𝓤 ̇) {{_ : Group H}} {{_ : Group G}} → 𝓤 ̇
IsSubgroup H G = Σ i ꞉ (H → G) , left-cancellable i × IsGroupHomomorphism H G i
}|
