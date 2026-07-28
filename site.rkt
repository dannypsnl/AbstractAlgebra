#lang racket/base
(require scribble/html)
(provide site)

(define site
  (hash 'description "Lectures of abstract algebra"
        'domain "dannypsnl.github.io/AbstractAlgebra"
        'title "abstract algebra"
        'head (list (script 'src: "/tiny.js" 'defer: #t)
                    (script 'src: "/fullTextSearch.js" 'defer: #t))))
