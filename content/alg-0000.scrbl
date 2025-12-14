@title{Group Theory}

@p{這裡我們開始介紹群論}
@transclude{group-0000}
@transclude{agda-0000}
@tr/card{
  @title{Basic facts about groups}

  @p{現在來看一些命題}
  @transclude{group-0001}
  @transclude{group-0002}
  @transclude{group-0003}
}
@transclude{group-0004}
@tr/card{
  @title{Basic facts of group homomorphism}

  @p{所以我們接著來看一個 group homomorphism 會有什麼特性。}
  @transclude{group-0005}
  @transclude{group-0006}
}
@transclude{group-0007}
@tr/card{
  @title{Basic facts of subgroup}

  @transclude{group-0008}
  @transclude{group-0009}
}
@transclude{group-000A}
@tr/card{
  @title{Basic facts of Kernel}

  @transclude{group-000B}
}
@tr/card{
  @title{Normal subgroup}
  @taxon{Definition}

  @p{如果 @m{G} 的@mention["group-0007"]{子群} @m{N} 對所有 @m{g \in G} 與 @m{n \in N} 滿足以下條件}
  @mm{
    g \bullet h \bullet g^{-1} \in N
  }
  @p{我們就說 @m{N} 是 Normal subgroup。}
}
@transclude{group-000C}
@transclude{group-000D}
