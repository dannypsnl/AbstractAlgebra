@title{(Left) Unit}

@agda|{
module ring-0007 where

open import MLTT.Spartan

open import ring-0000
open Ring {{...}}
}|

@ul{
  @li{@m{u} 是 left unit 的意思是存在 @m{v} 使 @m{u \cdot v = 1}}
  @li{@m{u} 是 right unit 的意思是存在 @m{v} 使 @m{v \cdot u = 1}}
}

@agda|{
is-left-unit : {R : 𝓤 ̇ } {{_ : Ring R}} → R → 𝓤 ̇
is-left-unit {_} {R} u = Σ v ꞉ R , u · v ＝ 1r

is-right-unit : {R : 𝓤 ̇ } {{_ : Ring R}} → R → 𝓤 ̇
is-right-unit {_} {R} u = Σ v ꞉ R , v · u ＝ 1r
}|
