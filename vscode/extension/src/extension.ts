import * as fs from "fs";
import * as os from "os";
import * as path from "path";

import axios from "axios";
import * as vscode from "vscode";
import {
  CloseAction,
  ErrorAction,
  Executable,
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";

import { Assistant } from "./assistant";

let client: LanguageClient;

let outputChannel: vscode.OutputChannel | undefined;

function log(message: string) {
  if (outputChannel === undefined) {
    outputChannel = vscode.window.createOutputChannel("Acorn Extension");
  }
  outputChannel.appendLine(message);
}

/**
 * Downloads a file from the given URL and saves it to the specified path.
 * @param url - The URL to download from.
 * @param filePath - The full path where the file will be saved.
 */
async function downloadFile(url: string, filePath: string): Promise<void> {
  let response = await axios.get(url, { responseType: "stream" });

  let fileStream = fs.createWriteStream(filePath);

  return new Promise((resolve, reject) => {
    response.data.pipe(fileStream);

    fileStream.on("finish", resolve); // Resolve on success
    fileStream.on("error", (err) => {
      fs.unlink(filePath, () => reject(err)); // Clean up on error
    });
  });
}

async function getProgress() {
  try {
    return await client.sendRequest("acorn/progress", {});
  } catch (e) {
    console.error("error in getProgress:", e);
    throw e;
  }
}

class ProgressTracker {
  // The time we started expecting a build.
  // Also acts as a flag for whether we are tracking.
  startTime: number | null;

  constructor() {
    this.startTime = null;
  }

  // Call this function when we expect a build soon.
  // It polls the language server for build progress and updates the UI.
  // Calling it multiple times is fine; subsequent simultaneous calls just return.
  // It returns when there is no longer an active build.
  async track() {
    if (this.startTime !== null) {
      return;
    }
    this.startTime = Date.now();
    try {
      await this.trackHelper();
    } catch (e) {
      console.error("error in progress tracker:", e);
    }
    this.startTime = null;
  }

  // Helper for track that does the actual work.
  // Doesn't finish until the active build completes.
  async trackHelper() {
    let response: any = await getProgress();

    while (response.done === response.total) {
      // Maybe progress just hasn't started yet.
      // Let's wait a bit and try again.
      await new Promise((resolve) => setTimeout(resolve, 100));
      response = await getProgress();

      let elapsed = Date.now() - this.startTime;
      if (elapsed > 2000) {
        // It's been a while. Let's give up.
        console.log("giving up on progress bar");
        return;
      }
    }

    let previousPercent = 0;
    await vscode.window.withProgress(
      {
        location: vscode.ProgressLocation.Notification,
        title: "Acorn Verification",
        cancellable: true,
      },
      async (progress, token) => {
        token.onCancellationRequested(() => {
          console.log("acorn verification progress bar canceled");
        });

        while (response.total !== response.done) {
          let percent = Math.floor((100 * response.done) / response.total);
          let increment = percent - previousPercent;
          progress.report({ increment });
          previousPercent = percent;

          // We have something to show, so we can wait a bit before updating.
          await new Promise((resolve) => setTimeout(resolve, 100));
          response = await getProgress();
        }
      }
    );
  }
}

let tracker = new ProgressTracker();

// Figures out where the server executable is.
// Downloads it if necessary.
async function getServerPath(
  context: vscode.ExtensionContext
): Promise<string> {
  let extension = vscode.extensions.getExtension(context.extension.id);
  let timestamp = new Date().toLocaleTimeString();
  let version = extension.packageJSON.version;
  let binName = `acornserver-${version}-${os.platform()}-${os.arch()}`;
  if (os.platform() === "win32") {
    binName += ".exe";
  }
  console.log(`activating ${binName} at`, timestamp);

  if (process.env.SERVER_PATH) {
    // Set explicitly in dev mode
    return process.env.SERVER_PATH;
  }

  // In production, the extension downloads a binary for the language server.
  let binDir = vscode.Uri.joinPath(context.globalStorageUri, "bin").fsPath;
  if (!fs.existsSync(binDir)) {
    fs.mkdirSync(binDir, { recursive: true });
    log(`created binary storage directory at ${binDir}`);
  }

  // Join the storage directory with the binary name
  let serverPath = path.join(binDir, binName);
  if (fs.existsSync(serverPath)) {
    // We already downloaded it
    return serverPath;
  }

  // Download the new binary from GitHub
  let oldBins = await fs.promises.readdir(binDir);
  let url = `https://github.com/acornprover/acorn/releases/download/v${version}/${binName}`;
  log(`downloading from ${url} to ${serverPath}`);
  await vscode.window.withProgress(
    {
      location: vscode.ProgressLocation.Notification,
      title: `Downloading ${binName} from GitHub...`,
      cancellable: false,
    },
    async () => {
      try {
        await downloadFile(url, serverPath);
      } catch (e) {
        // Pop up an error message
        vscode.window.showErrorMessage(
          `failed to download Acorn language server: ${e.message}`
        );
        log(`error downloading {url}: {e.message}`);
        throw e;
      }
    }
  );
  // Make the binary executable
  if (os.platform() !== "win32") {
    await fs.promises.chmod(serverPath, 0o755);
  }
  log("download complete");

  // Remove old binaries
  for (let oldBin of oldBins) {
    if (oldBin === binName) {
      // This shouldn't happen
      throw new Error("unexpected redownload");
    }
    let oldBinPath = path.join(binDir, oldBin);
    log(`removing old binary ${oldBinPath}`);
    fs.unlinkSync(oldBinPath);
  }

  return serverPath;
}

async function registerCommands(context: vscode.ExtensionContext) {
  let disposable = vscode.commands.registerCommand(
    "acorn.newFile",
    async () => {
      let document = await vscode.workspace.openTextDocument({
        language: "acorn",
      });
      await vscode.window.showTextDocument(document);
    }
  );
  context.subscriptions.push(disposable);
}

export async function activate(context: vscode.ExtensionContext) {
  let command = await getServerPath(context);

  // Add workspace root argument if available
  let args = ["--extension-root", context.extensionPath];
  if (
    vscode.workspace.workspaceFolders &&
    vscode.workspace.workspaceFolders.length > 0
  ) {
    let workspaceRoot = vscode.workspace.workspaceFolders[0].uri.fsPath;
    args.push("--workspace-root", workspaceRoot);
  }

  let exec: Executable = {
    command,
    args,
    options: {
      env: {
        RUST_BACKTRACE: "1",
        ...process.env,
      },
    },
  };

  // Currently we don't do anything differently in debug mode.
  let serverOptions: ServerOptions = {
    run: exec,
    debug: exec,
  };

  let initFailed = false;

  let clientOptions: LanguageClientOptions = {
    // Register the server for plain text documents
    documentSelector: [{ scheme: "file", language: "acorn" }],
    synchronize: {
      // Notify the server about file changes to '.clientrc files contained in the workspace
      fileEvents: vscode.workspace.createFileSystemWatcher("**/.clientrc"),
    },
    initializationFailedHandler: (error) => {
      initFailed = true;
      vscode.window.showErrorMessage("Acorn error: " + error.message);
      // Prevent automatic restart
      return false;
    },
    errorHandler: {
      error: (error, message, count) => {
        console.error("Language server error:", error);
        // Do not restart on error
        return { action: ErrorAction.Shutdown, handled: initFailed };
      },
      closed: () => {
        console.warn("Language server process closed.");
        // Do not restart on process close
        return { action: CloseAction.DoNotRestart, handled: initFailed };
      },
    },
  };

  // Create the language client and start the client.
  client = new LanguageClient(
    "acornLanguageServer",
    "Acorn Language Server",
    serverOptions,
    clientOptions
  );

  // Start the client. This will also launch the server
  try {
    await client.start();
  } catch (e) {
    console.error("client failed to start:", e);
    return;
  }

  let assistantPath = context.asAbsolutePath("build/assistant");
  let assistant = new Assistant(client, assistantPath);
  context.subscriptions.push(assistant);

  let onSaveOrOpen = async (document: vscode.TextDocument) => {
    if (document.languageId !== "acorn") {
      return;
    }
    assistant.autoDisplay(document);
    await tracker.track();
  };

  for (let doc of vscode.workspace.textDocuments) {
    if (doc.languageId === "acorn") {
      assistant.autoDisplay(doc);
      // No await, because we don't want to block the UI thread.
      tracker.track();
      break;
    }
  }

  await registerCommands(context);
  context.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(onSaveOrOpen)
  );
  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(onSaveOrOpen)
  );
}

export function deactivate(): Thenable<void> | undefined {
  if (!client || !client.isRunning()) {
    return undefined;
  }
  return client.stop();
}
