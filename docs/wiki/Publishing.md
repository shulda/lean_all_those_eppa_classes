# Publishing the documentation to the GitHub Wiki tab

These research notes are maintained in the main repository at
[`docs/wiki/`](./README.md). They are synchronized by
[`.github/workflows/publish-wiki.yml`](../../.github/workflows/publish-wiki.yml)
to the **separate** Wiki Git repository shown at
https://github.com/shulda/lean_all_those_eppa_classes/wiki.

This setup follows
[the Milliken wiki's publishing design](https://github.com/janhubicka/lean-milliken/blob/main/docs/wiki/Publishing.md).

## Initializing a newly enabled Wiki: one-time user action

Enabling the GitHub Wiki feature is not the same as creating
its separate `.wiki.git` repository. GitHub generally requires
the **first** page to be created in the web Wiki editor:

1. While signed in with Wiki edit permission, open
   https://github.com/shulda/lean_all_those_eppa_classes/wiki.
2. If prompted to create the first page, title it **Home**.
   Temporary text such as “Published automatically from docs/wiki”
   is sufficient. Save the page.
3. Saving triggers GitHub's `gollum` event; the workflow should
   synchronize the full documentation automatically. If it
   does not, open the repository's **Actions → Publish EPPA wiki**
   workflow and select **Run workflow** on `main`.

**Do this only if GitHub still shows “Create the first page”.**
If the Wiki repository already exists, no manual bootstrap is
necessary. The publishing job explicitly tests `.wiki.git`
and reports a notice if it has not yet been initialized.

## What publishes, and when

The workflow runs when `docs/wiki/**` or its own workflow
changes on `main`, on `gollum` events and on manual dispatch.
It uses `Andrew-Chen-Wang/github-wiki-action@v5`,
matching the Milliken project, with preprocessing enabled:

- `docs/wiki/README.md` becomes the Wiki's `Home.md`.
- The other Markdown pages become Wiki pages.
- Links to neighboring Wiki pages are rewritten appropriately;
  links outside `docs/wiki/` are rewritten to source-repository
  URLs at a documented revision.
- The sync does not force-push the Wiki Git repository.

The **source-controlled docs**, rather than direct Wiki-tab
edits, are authoritative. Correct mathematical statements via
reviewed commits in `docs/wiki/`; edits made directly to the
Wiki tab may be overwritten by synchronization.

If publishing reports a permissions error, check repository
Actions permissions for a `contents: write` workflow. The
Lean proof build workflow is separate and remains read-only.

The [version-controlled front page](README.md) remains
readable from GitHub even before Wiki initialization.
