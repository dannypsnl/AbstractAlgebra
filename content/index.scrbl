@title{Lectures of abstract algebra}

@p{數學是非常難學的，因為數學需要大量的練習才能真正掌握。一般教科書的證明，通常會提點一些大方向，或是用上讀者不懂的其他「常識」，就算是證明完畢，剩下的讓讀者自己練習填上。如果是在課堂上學習，倒也還能跟助教、老師詢問，但自學的人要怎麼知道自己寫的證明正確無誤呢？我認為 Agda 或是 Lean 這類的定理證明器就可以幫上忙，除了能夠證明你寫下的程式正確，用自己的想法把數學陳述寫成程式並證明，本身就是有益的練習。}

@p{我把初等的抽象代數事實整理成這個網站，把一些代數的事實紀錄下來，既可以用做查詢，也可以讓初學者當作學習的補充材料。}
@blockquote{請用 @kbd{Cmd + K} 或是 @kbd{Ctrl + K} 查詢內容}
@p{有興趣嘗試證明器的讀者更是可以試著 fork 專案 @external{https://github.com/dannypsnl/AbstractAlgebra} 練習更多的延伸命題，用 Agda 學習抽象代數。}
@transclude[#:open #f]{alg-0000}
@transclude[#:open #f]{alg-0001}
@transclude[#:open #f]{recent-changes}

@footer{
  @address['class: "address-block"]{
    @ul['aria-label: "About" 'role: "list"]{
      @li{
        @span['aria-hidden: "true"]{訂閱}
        @a['href: "/rss.xml" 'aria-label: "rss"]{
          @svg[
            'class: "prefix-icon" 'width: 16 'height: 16
            'viewBox: "0 0 24 24"
          ]{
            @path['d: "M3 3c9.941 0 18 8.059 18 18h-3c0-8.284-6.716-15-15-15V3Zm0 7c6.075 0 11 4.925 11 11h-3a8 8 0 0 0-8-8v-3Zm0 7a4 4 0 0 1 4 4H3v-4Z"]
          }
        }
        @span['aria-hidden: "true"]{RSS 可以看到更新進度}
      }
    }
  }
  @div['class: "copyright-container"]{
    @div['class: "copyright"]{Copyright © Content is available under @a['href: "https://choosealicense.com/licenses/cc0-1.0/"]{CC0 1.0 Universal} unless otherwise noted.}
    @div['class: "cc-badge"]{
      @a['ref: "license" 'href: "https://choosealicense.com/licenses/cc0-1.0/"]{
        @img['alt: "Creative Commons License" 'src: "https://licensebuttons.net/l/zero/1.0/88x31.png"]
      }
    }
  }
}
