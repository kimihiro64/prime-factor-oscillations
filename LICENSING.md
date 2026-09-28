# Licensing scope

The single repository-level licence for Prime Factor Oscillations is the
[Apache License 2.0](LICENSE), as recorded by `project.license` in
`formalization.yaml`. Except where a file says otherwise, Apache-2.0 applies
to the copyrightable interests that project contributors are authorized to
license in original repository material, including Lean source, scripts,
configuration, project documentation, and project-authored data arrangements.

## Research paper

The original expression in `paper/research-paper.tex` and the PDF built from
it is available, at the recipient's choice, under either:

- Apache License 2.0; or
- [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/)
  (`CC-BY-4.0`).

The paper carries this notice in both its source and rendered PDF. This
additional option does not replace or make ambiguous the repository's
Apache-2.0 default.

## Mathematics, sources, and dependencies

Licensing and scholarly provenance are separate:

- This repository does not claim ownership of mathematical statements, facts,
  methods, or results. Attribution and the relationship between cited sources
  and Lean declarations are recorded in `formalization.yaml` and the research
  paper.
- Cited papers and supplied literature retain their own copyrights and terms
  of access. The repository licence does not relicense them.
- Git dependencies named in `lake-manifest.json` and the Lean toolchain retain
  their own licences and copyright notices.
- A file incorporating third-party copyrightable material remains subject to
  the third party's notice and licence as well as any licence applying to
  project-authored modifications.

## Generated distributions

The initial publication distributes project source, documentation and artifact
hash manifests. It includes no dependency-cache archive, CI workflow or
generated API-documentation archive. Obtain Erdos 690's compiled cache from
its own release, preserving that release's notices.

Any future distribution of compiled artifacts or generated documentation must
carry the applicable project, Lean and dependency notices. Generated
documentation that includes transitive imports is an aggregate and does not
change the licences applying to third-party material.

## Contributions

Unless explicitly agreed and marked otherwise, contributions are accepted
under Apache-2.0. Contributors must preserve applicable third-party notices
and submit only material they are authorized to license.
