(lang dune 3.21)

(generate_opam_files true)

(name rocq-faial)
(version 0.1.0)

(package
 (name rocq-faial)
 (synopsis "Faial: formal semantics and barrier alignment for GPU kernels")
 (description "Coq/Rocq formalization of Faial: a hierarchy of languages for GPU kernels (ULang, WLang, ALang, TLang) along with barrier-alignment, phase-splitting and sequentialization theorems.")
 (maintainers "Tiago Cogumbreiro <cogumbreiro@users.sf.net>")
 (authors "Tiago Cogumbreiro <cogumbreiro@users.sf.net>")
 (license "Unlicense")
 (depends
  (rocq-prover (>= 9.0))
  (rocq-stdlib (>= 9.0))
  (rocq-aniceto (>= 1.0.0))
  (dune (>= 3.0))))

(using rocq 0.11)
