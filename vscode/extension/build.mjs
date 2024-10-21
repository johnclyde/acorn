import { build } from 'esbuild';

build({
  entryPoints: ['src/extension.ts'],
  outfile: 'build/extension/bundle.js',
  bundle: true,
  sourcemap: true,
  platform: 'node',
  target: 'es2020',
  external: ['vscode'],
}).catch(() => process.exit(1));
