@title{Non zero-divisor}
@taxon{Definition}

@agda|{
module ring-0004 where

open import MLTT.Spartan

open import ring-0000
open Ring {{...}}
}|

@p{一個 Ring @m{R} 中的元素 @m{a} 是 zero divisor 就表示存在 @m{b \ne 0 \in R} 使 @m{a b = 0}。
所以我們稱 @m{a} 是 non zero-divisor 指如果 @m{ab=0}，那 @m{b} 一定等於 @m{0}。}

@agda|{
NonZeroDivisor : {R : 𝓤 ̇ } {{_ : Ring R}} (a : R) → 𝓤 ̇
NonZeroDivisor {_}{R} a = (b : R) → (a · b ＝ 0r → b ＝ 0r)
}|
