(lang dune 3.8)
(using coq 0.8)
(name mirrorsolve)

(generate_opam_files true)

(package 
 (name mirrorsolve)
 (depends 
  (coq-equations (>= 1.3))
  coq-metacoq-template
  coq-metacoq-translations
  coq-metacoq
  (coq (>= 8.18))
  ocaml-lsp-server
  coq-hammer
  (camlp-streams (>= 5.0.1))
 )
 (synopsis "SMT integration for Coq using reflection")
 (description  "SMT integration for Coq using reflection")
 (maintainers   "sarracino2@llnl.gov")
 (authors      "John Sarracino" "Ryan Doenges" "Tobias Kappe")
 (homepage     "https://github.com/jsarracino/mirrorsolve")
 (bug_reports  "https://github.com/jsarracino/mirrorsolve")
)
