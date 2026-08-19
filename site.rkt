#lang racket/base
(require scribble/html)
(require racket/file
         racket/path
         gregor
         (prefix-in rss: tr/rss)
         (prefix-in meta: tr/meta))
(provide site)

(define site-title "abstract algebra")
(define site-domain "dannypsnl.github.io/AbstractAlgebra")
(define site-description "Lectures of abstract algebra")

(define (build-rss! output-dir)
  (define (meta->datetime meta)
    (define date (hash-ref meta 'date #f))
    (unless (string? date)
      (error 'build-rss!
             "post ~s (id ~s) has no `date`; add a `date` line to its .scrbl so it can appear in the RSS feed"
             (hash-ref meta 'title "<untitled>")
             (hash-ref meta 'id "<unknown>")))
    (iso8601->datetime date))

  (define (scrbl-addr path)
    (path->string (path-replace-extension (file-name-from-path path) #"")))

  (define entries
    (sort (for/list ([path (find-files (lambda (p) (path-has-extension? p #".scrbl")) "content/post")])
            (meta:card-metadata (scrbl-addr path)))
          (lambda (a b) (datetime>=? (meta->datetime a) (meta->datetime b)))))

  (define items
    (for/list ([meta entries])
      (define body (file->string (build-path "_tmp" (string-append (hash-ref meta 'id) ".embed.html"))))
      (rss:item
        (rss:title (hash-ref meta 'title))
        (rss:link (string-append "https://" site-domain "/" (hash-ref meta 'id)))
        (rss:description body)
        (rss:content-encoded (rss:cdata body))
        (rss:pubDate (~t (meta->datetime meta) "EEE, dd MMM yyyy HH:mm:ss +0800")))))

  (define rss-path (build-path output-dir "rss.xml"))
  (call-with-output-file rss-path #:exists 'truncate/replace
    (lambda (out)
      (display (rss:create-feed #:title site-title #:link site-domain #:description site-description items) out))))

(define site
  (hash 'description site-description
        'domain site-domain
        'title site-title
        'html-lang "zh-TW"
        'after-build build-rss!
        'head (list (link 'rel: "stylesheet" 'href: "/custom-style.css")
                    (script 'src: "/tiny.js" 'defer: #t)
                    (script 'src: "/fullTextSearch.js" 'defer: #t))))
