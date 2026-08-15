# Export to Rodin

When the model is ready, hand it to the Rodin platform:

- **Open in Rodin** — click the code lens shown above every `MACHINE` or
  `CONTEXT` header. The language server builds the model into a persistent
  Rodin workspace (`.rossi/rodin` next to your sources — consider adding
  `.rossi/` to your `.gitignore`) and launches the Rodin IDE on it. Proofs
  you make in Rodin live in that workspace and survive rebuilds: unchanged
  proof obligations keep their stamps and statuses when you re-run the lens
  after editing the model.
- **Rossi: Export Current File to Rodin ZIP** — produce a one-off Rodin
  project archive instead.

Set `rossi.rodin.path` if Rodin is not installed at the platform default
location, and `rossi.rodin.workspace` to relocate the shared workspace.
