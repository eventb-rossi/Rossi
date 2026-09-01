/**
 * Standalone tests for the extension manifest's setting scopes. No VSCode
 * required.
 *
 *   npm run test:manifest
 *
 * The settings that name a program the extension runs must stay out of
 * workspace settings. Nothing else in the build inspects `contributes`, so a
 * dropped `scope` would reopen that hole silently.
 *
 * Exits non-zero on the first failure so it can gate CI / pre-commit.
 */
import * as fs from 'fs';
import * as path from 'path';

let failures = 0;
function check(name: string, condition: boolean): void {
    if (condition) {
        console.log(`ok   ${name}`);
    } else {
        console.error(`FAIL ${name}`);
        failures += 1;
    }
}

// Read rather than import: tsconfig's rootDir is `src`, so importing JSON from
// the package root would rearrange the `out/` layout.
const manifest = JSON.parse(fs.readFileSync(path.join(__dirname, '..', 'package.json'), 'utf8'));
const properties: Record<string, { scope?: string }> = manifest.contributes.configuration.properties;
const untrusted = manifest.capabilities?.untrustedWorkspaces;
const restricted: string[] = untrusted?.restrictedConfigurations ?? [];

// Matched by shape rather than by list, so a newly added executable path
// cannot slip in unscoped.
const executablePaths = Object.keys(properties).filter(key => key.endsWith('.path'));

for (const key of ['rossi.tool.path', 'rossi.languageServer.path', 'rossi.rodin.path', 'rossi.animate.path']) {
    check(`${key} is still declared`, executablePaths.includes(key));
}
for (const key of executablePaths) {
    check(`${key} is machine-scoped`, properties[key].scope === 'machine');
}
check(
    'rossi.rodin.workspace is machine-overridable',
    properties['rossi.rodin.workspace']?.scope === 'machine-overridable'
);

check('untrusted workspaces are supported with limits', untrusted?.supported === 'limited');
check(
    'the limitation is explained to the user',
    typeof untrusted?.description === 'string' && untrusted.description.length > 0
);
for (const key of [...executablePaths, 'rossi.rodin.workspace']) {
    check(`${key} is restricted in untrusted workspaces`, restricted.includes(key));
}
for (const key of restricted) {
    check(`restricted ${key} is a declared setting`, key in properties);
}

if (failures > 0) {
    console.error(`\n${failures} manifest test(s) failed.`);
    process.exit(1);
}
console.log('\nAll manifest tests passed.');
