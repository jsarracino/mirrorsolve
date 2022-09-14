(lang dune 2.2)
(using coq 0.1)
(name mirrorsolve)

(generate_opam_files true)

(package 
 (name mirrorsolve)
 (depends 
  (coq-equations (>= 1.3))
  (coq-metacoq-template (= 1.0+8.15))
  (coq-metacoq-translations (= 1.0+8.15))
  (coq-metacoq (= 1.0+8.15))
  (coq (and (>= 8.15) (< 8.16)))
 )
 (synopsis "SMT integration for Coq using reflection")
 (description  "SMT integration for Coq using reflection")
 (maintainers   "jsarracino@cornell.edu")
 (authors      "John Sarracino" "Ryan Doenges" "Tobias Kappé")
 (homepage     "https://github.com/jsarracino/mirrorsolve")
 (bug_reports  "https://github.com/jsarracino/mirrorsolve")
)
