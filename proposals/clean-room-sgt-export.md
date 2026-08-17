# Proposal: Clean-Room SGT Export

**Status:** Proposed. This document authorizes no copying, deletion, history
rewrite, publication, or repository creation.

## Decision

Create a new repository from a deliberately selected set of clean files,
rather than trying to scrub this repository's history. Treat the current
repository as quarantined: it may contain patent-sensitive research context
and must not supply application-specific language, examples, rationale, or
implementation.

This is an exposure-reduction plan, not legal advice or a determination of
patentability, prior disclosure, or freedom to operate. Patent counsel should
approve the selection and publication boundary.

## Clean-room rule

Every item entering the new repository must be justified from public,
independently useful SGT requirements. It must not be selected because it
supports, describes, or remembers a protected application or external
research project.

Do not copy Git history, `.git` metadata, branches, tags, release notes,
commit messages, application-specific modules, derived examples, strategy or
activity records, research-archive material, ignored external-project content,
raw agent transcripts, or private notes.

## Candidate inclusion test

A file is eligible only if all answers are yes:

1. Does it expose a general SGT definition, theorem interface, or utility
   with a plausible consumer unrelated to the protected application?
2. Can its API, comments, tests, and examples be explained only in neutral
   mathematical terms?
3. Does it have public provenance and no private or application-specific
   rationale embedded in source or documentation?
4. Can it be recreated or independently reviewed in the new repository
   without consulting quarantined material?

Anything uncertain stays out pending counsel and independent technical review.

## Export workflow

1. Create a new empty repository with a new initial commit; do not fork or
   clone this repository.
2. Start with a minimal public scope: build configuration, license, neutral
   README, and a reviewed SGT core.
3. Recreate or copy only approved mathematical files into a clean staging
   directory outside both repositories. Review comments, docstrings, test
   names, imports, generated artifacts, and filenames before adding them.
4. Rebuild indices, QA scoreboard, documentation, and the umbrella import from
   selected files; never copy generated status/history documents.
5. Run a private, counsel-approved terminology scan and manual public-entry
   review before the first push.
6. Require a second reviewer to verify every included file passes the test and
   no omitted path is imported transitively.
7. Publish only after written approval of the clean tip. Preserve the audit
   record outside the public repository.

## Initial public boundary

Favor a small foundation over breadth: graph and Laplacian definitions,
neutral spectral/variational interfaces, and only QA needed to establish their
public shape. Add broader material only after a fresh inclusion review.

No compatibility promise is owed to this repository. If a declaration is
useful but its provenance or framing is uncertain, rederive and reimplement
it independently or leave it out.

## Handling the current repository

- Do not claim it has been scrubbed merely because a new repository exists.
- Restrict access and avoid new public disclosures until counsel advises
  otherwise.
- Do not link the new repository to it in public docs, package metadata,
  migration guides, or commit messages.
- If counsel later requires historical removal, treat that as a separate,
  coordinated operation. GitHub notes that history rewriting can be
  recontaminated by old clones or forks and may require hosting-side cleanup;
  see [GitHub's sensitive-data-removal guidance](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/removing-sensitive-data-from-a-repository).

## Approval gate

Before creating the new public repository, obtain an explicit decision on the
approved initial file list, private terminology/provenance review, required
reviewers and counsel sign-off, and access/publication rules for this
quarantined repository.
