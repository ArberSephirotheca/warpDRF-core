(lang dune 3.21)

(generate_opam_files true)

(name rocq-faial)
(version 0.1.0)

(package
 (name rocq-faial)
 (synopsis "Faial: Rocq formalizations of GPU kernel analyses")
 (description "Rocq formalizations of memory access pattern (MAP) analyses for GPU kernels: the Drf theory covers barrier alignment, phase-splitting and sequentialization of a ULang/WLang/ALang/TLang hierarchy; the Approx theory covers the approximation analysis with control-flow and data-independence judgments, dependency analysis, and soundness wrt true data-races.")
 (maintainers "Tiago Cogumbreiro <cogumbreiro@users.sf.net>")
 (authors "Tiago Cogumbreiro <cogumbreiro@users.sf.net>")
 (license "Unlicense")
 (depends
  (rocq-prover (>= 9.0))
  (rocq-stdlib (>= 9.0))
  (rocq-aniceto (>= 1.0.0))
  (dune (>= 3.0))))

(using rocq 0.11)
