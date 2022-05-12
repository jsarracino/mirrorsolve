(lang dune 2.2)
(using coq 0.1)
(name mirrorsolve)

(generate_opam_files true)

(package 
 (name mirrorsolve)
 (depends 
  (coq-equations (= 1.3~beta1+8.13))
  (coq (>= 8.13.0))
  (coq-metacoq-template (= 1.0~beta2+8.13))
 )
 (synopsis "SMT integration for Coq using reflection")
 (description  "SMT integration for Coq using reflection")
 (maintainers   "jsarracino@cornell.edu")
 (authors      "John Sarracino" "Ryan Doenges" "Tobias Kappé")
 (homepage     "https://github.com/jsarracino/mirrorsolve")
 (bug_reports  "https://github.com/jsarracino/mirrorsolve")
 (license      "GPL 3")
)
