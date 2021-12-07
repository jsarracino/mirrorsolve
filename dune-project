(lang dune 2.2)
(using coq 0.1)
(name mirrorsolve)

(generate_opam_files true)

(package 
 (name mirrorsolve)
 (depends 
  (coq (>= 8.13.0))
 )
 (synopsis "SMT integration for Coq using reflection")
 (description  "SMT integration for Coq using reflection")
 (maintainers   "jsarracino@cornell.edu")
 (authors      "John Sarracino" "Ryan Doenges" "Tobias Kappé")
 (homepage     "https://github.com/jsarracino/mirrorsolve")
 (bug_reports  "https://github.com/jsarracino/mirrorsolve")
 (license      "GPL 3")
)
