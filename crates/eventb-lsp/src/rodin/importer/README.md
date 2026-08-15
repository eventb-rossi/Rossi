# Rodin project importer

The **Open in Rodin** code lens needs to register the project it builds into
the shared Rodin workspace *before* launching Rodin, so the project shows up
without a manual `File → Import`. The robust, version-independent way to do
that is to ask Eclipse itself, via its headless Ant runner
(`org.eclipse.ant.core.antRunner`, bundled with Rodin), to load the `.project`
descriptor and create/open the project through the Eclipse Resources API.

That work is done by a tiny Ant task, [`RodinProjectImportTask.java`](./RodinProjectImportTask.java).

## Why a precompiled class is embedded

The language server cannot assume a JDK is installed on the user's machine, so
it **ships the compiled class** rather than compiling on demand.
[`RodinProjectImportTask.class`](./RodinProjectImportTask.class) is the
canonical copy: it is embedded into the server binary via `include_bytes!` in
[`../launch.rs`](../launch.rs). At runtime the server writes it into the
workspace's transient `.rossi-importer/org/rossi/vscode/` directory (the class
keeps its historical `org.rossi.vscode` package name — renaming it would force
a recompile for zero benefit), generates a small `build.xml`, and runs it
through Rodin's Ant runner.

`RodinProjectImportTask.java` is the human-readable source, kept next to the
class for review; it is not compiled by any build step.

## Regenerating

Requires a JDK 17 and the Apache Ant + Eclipse Platform resources/runtime APIs
that Rodin bundles (their exact bundle versions vary by Rodin release):

```bash
# Compile against Rodin's bundled jars (adjust the plugins path/versions).
RODIN_PLUGINS=/Applications/Rodin.app/Contents/Eclipse/plugins   # macOS example
mkdir -p out
javac --release 17 -d out \
  -cp "$RODIN_PLUGINS/org.apache.ant_*/lib/ant.jar:\
$RODIN_PLUGINS/org.eclipse.core.resources_*.jar:\
$RODIN_PLUGINS/org.eclipse.core.runtime_*.jar:\
$RODIN_PLUGINS/org.eclipse.equinox.common_*.jar" \
  crates/eventb-lsp/src/rodin/importer/RodinProjectImportTask.java
cp out/org/rossi/vscode/RodinProjectImportTask.class crates/eventb-lsp/src/rodin/importer/
```

The server picks the new class up on the next `cargo build`.
