@title{(Left) Action}

@agda|{
module ring-0006 where

open import MLTT.Spartan

open import ring-0000
open Ring {{...}}
}|

@p{一個 Ring @m{R} 中的元素 @m{a} 所謂的 (left) action 是指}

@mm{
x \mapsto a \cdot x
}

@p{@m{R \to R} 這樣的 map，通常記為 @m{L_a}。所謂的 (right) action 可想而知，在乘法交換的 commutative ring 中兩種 action 並沒有差異，這時候定義通常跟那個領域的慣例有關。}

@agda|{
left-action : {R : 𝓤 ̇ } {{_ : Ring R}} (a : R) → R → R
left-action a x = a · x

right-action : {R : 𝓤 ̇ } {{_ : Ring R}} (a : R) → R → R
right-action a x = x · a
}|
