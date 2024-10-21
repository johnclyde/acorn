import {
  ExtensionContext,
  extensions,
  ProgressLocation,
  TextDocument,
  Uri,
  window,
  workspace,
} from "vscode";
import * as fs from "fs";
import * as os from "os";
import {
  CloseAction,
  ErrorAction,
  Executable,
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";
import { SearchPanel } from "./search-panel";

let client: LanguageClient;

async function getProgress() {
  try {
    return await client.sendRequest("acorn/progress", {});
  } catch (e) {
    console.error("error in getProgress:", e);
    throw e;
  }
}

// Automatically hides it when we are done.
async function showProgressBar() {
  let startTime = Date.now();

  try {
    let response: any = await getProgress();

    while (response.done === response.total) {
      // Maybe progress just hasn't started yet.
      // Let's wait a bit and try again.
      await new Promise((resolve) => setTimeout(resolve, 100));
      response = await getProgress();

      let elapsed = Date.now() - startTime;
      if (elapsed > 2000) {
        // It's been a while. Let's give up.
        console.log("giving up on progress bar");
        return;
      }
    }

    let previousPercent = 0;
    window.withProgress(
      {
        location: ProgressLocation.Notification,
        title: "Acorn Validation",
        cancellable: true,
      },
      async (progress, token) => {
        token.onCancellationRequested(() => {
          console.log("acorn validation progress bar canceled");
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
  } catch (e) {
    console.error("error showing progress bar:", e);
  }
}

// Figures out where the server executable is.
// Downloads it if necessary.
async function getServerPath(context: ExtensionContext) {
  let extension = extensions.getExtension(context.extension.id);
  let timestamp = new Date().toLocaleTimeString();
  let version = extension.packageJSON.version;
  let bin = `acornserver-v${version}-${os.platform()}-${os.arch()}`;
  console.log(`activating ${bin} at`, timestamp);

  if (process.env.SERVER_PATH) {
    // Set explicitly in dev mode
    return process.env.SERVER_PATH;
  }

  // In production, the extension downloads a binary for the language server.
  let storageDir = context.globalStorageUri.fsPath;
  if (!fs.existsSync(storageDir)) {
    fs.mkdirSync(storageDir, { recursive: true });
    console.log(`Created global storage directory at ${storageDir}`);
  }

  let serverPath = Uri.joinPath(context.globalStorageUri, bin).fsPath;
  if (fs.existsSync(serverPath)) {
    // We already downloaded it
    return serverPath;
  }

  let message = `TODO: download binary into ${serverPath}`;
  console.log(message);
  window.showErrorMessage(message);
  throw new Error(message);
}

export async function activate(context: ExtensionContext) {
  let traceOutputChannel = window.createOutputChannel("Acorn Language Server");

  let command = await getServerPath(context);

  let exec: Executable = {
    command,
    options: {
      env: {
        RUST_BACKTRACE: "1",
        ...process.env,
      },
    },
  };

  // If the extension is launched in debug mode then the debug server options are used
  // Otherwise the run options are used
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
      fileEvents: workspace.createFileSystemWatcher("**/.clientrc"),
    },
    traceOutputChannel,
    initializationFailedHandler: (error) => {
      initFailed = true;
      window.showErrorMessage("Acorn error: " + error.message);
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
    "acornClient",
    "Acorn Client",
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

  let searchPath = context.asAbsolutePath("build/search");
  context.subscriptions.push(new SearchPanel(client, searchPath));

  let onDocumentChange = async (document: TextDocument) => {
    if (document.languageId !== "acorn") {
      return;
    }
    await showProgressBar();
  };

  let hasAcornDocs = false;
  for (let doc of workspace.textDocuments) {
    if (doc.languageId === "acorn") {
      hasAcornDocs = true;
      break;
    }
  }

  if (hasAcornDocs) {
    showProgressBar();
  }

  context.subscriptions.push(workspace.onDidSaveTextDocument(onDocumentChange));
  context.subscriptions.push(workspace.onDidOpenTextDocument(onDocumentChange));
}

export function deactivate(): Thenable<void> | undefined {
  if (!client || !client.isRunning()) {
    return undefined;
  }
  return client.stop();
}
