import {
  commands,
  Disposable,
  Position,
  Range,
  TextEditor,
  TextEditorRevealType,
  TextEditorSelectionChangeKind,
  Uri,
  ViewColumn,
  WebviewPanel,
  window,
  workspace,
} from "vscode";
import * as fs from "fs";
import * as path from "path";
import { LanguageClient } from "vscode-languageclient/node";

const showLocationDecoration = window.createTextEditorDecorationType({
  backgroundColor: "rgba(246, 185, 77, 0.3)",
});

export class Assistant implements Disposable {
  client: LanguageClient;
  currentParams: SearchParams;
  currentSearchId: number;
  disposables: Disposable[];
  distPath: string;
  listener: Disposable;
  panel: WebviewPanel;
  requestViewColumn: number;
  wasShown: boolean;

  constructor(client: LanguageClient, distPath: string) {
    this.client = client;
    this.distPath = distPath;
    this.currentSearchId = 0;
    this.wasShown = false;
    this.disposables = [
      commands.registerTextEditorCommand("acorn.showAssistant", (editor) =>
        this.show(editor)
      ),

      commands.registerTextEditorCommand("acorn.toggleAssistant", (editor) =>
        this.toggle(editor)
      ),
      window.onDidChangeTextEditorSelection(async (e) => {
        if (
          e.kind === TextEditorSelectionChangeKind.Mouse ||
          e.kind === TextEditorSelectionChangeKind.Keyboard
        ) {
          // We only want to trigger on explicit user actions.
          await this.searchOnSelection(true);
        }
      }),
      workspace.onDidSaveTextDocument(async () => {
        this.chooseHelp();
        await this.searchOnSelection(false);
      }),
      window.onDidChangeActiveTextEditor(async () => {
        this.chooseHelp();
      }),
    ];
  }

  sendHelp(help: Help) {
    this.panel.webview.postMessage({ type: "help", help });
  }

  // Sends an appropriate help object, based on the active editor.
  chooseHelp() {
    let editor = window.activeTextEditor;
    if (!editor || !editor.document || !this.panel) {
      return;
    }
    let document = editor.document;
    if (document.languageId !== "acorn") {
      return;
    }

    if (document.uri.scheme !== "file") {
      // This is an untitled file.
      this.sendHelp({ newDocument: true });
      return;
    }

    // Heuristic, just when to stop telling people "type in a theorem now please"
    for (let i = 0; i < document.lineCount; i++) {
      const line = document.lineAt(i);
      let trim = line.text.trim();
      if (
        trim.length > 0 &&
        !trim.startsWith("//") &&
        !trim.startsWith("from") &&
        !trim.startsWith("import")
      ) {
        // There may actually be a selection. But the assistant knows to use the search result
        // if there is one. So, send the help message for there not being a selection.
        this.sendHelp({ noSelection: true });
        return;
      }
    }

    // This document just doesn't have any real stuff in it.
    this.sendHelp({ newDocument: true });
  }

  // Runs a new search based on the current selection.
  // If 'onSelect' is passed, just the selection changed.
  async searchOnSelection(onSelect: boolean) {
    try {
      let editor = window.activeTextEditor;
      if (
        !editor ||
        !editor.document ||
        editor.document.languageId !== "acorn" ||
        editor.document.uri.scheme !== "file" ||
        !this.panel
      ) {
        return;
      }

      // Clear any showLocation highlighting
      editor.setDecorations(showLocationDecoration, []);

      let uri = editor.document.uri.toString();
      let selectedLine = editor.selection.start.line;
      let version = editor.document.version;

      // Check if we are just selecting a different part of the same target.
      if (
        onSelect &&
        this.currentParams &&
        this.currentParams.uri === uri &&
        this.currentParams.selectedLine === selectedLine
      ) {
        return;
      }

      let id = this.currentSearchId + 1;
      let params: SearchParams = { uri, selectedLine, version, id };

      // This view column is probably the one the user is actively writing in.
      // When in doubt, we can use this view column to do code-writing operations.
      this.requestViewColumn = editor.viewColumn;

      await this.sendSearchRequest(params);
    } catch (e) {
      console.error("error during update:", e);
    }
  }

  // Sends a search request to the language server, passing the response on to the webview.
  async sendSearchRequest(params: SearchParams) {
    console.log(
      `search request ${params.id}: ${params.uri} v${params.version} line ${params.selectedLine}`
    );
    this.currentSearchId = params.id;
    this.currentParams = params;

    while (true) {
      let response: SearchResponse = await this.client.sendRequest(
        "acorn/search",
        params
      );

      if (!this.panel || params.id != this.currentSearchId) {
        // The request is no longer relevant
        return;
      }
      if (response.failure) {
        console.log("search failure:", response.failure);
        return;
      }
      if (!response.loading) {
        this.panel.webview.postMessage({ type: "search", response });
      }

      if (response.status.outcome !== null) {
        // The search is complete.
        return;
      }

      // The search is not complete. Send another request after waiting a bit.
      let ms = 50;
      await new Promise((resolve) => setTimeout(resolve, ms));
      if (!this.panel || params.id != this.currentSearchId) {
        return;
      }
    }
  }

  // Handles messages from the webview.
  async handleWebviewMessage(message: any) {
    try {
      if (message.command === "insertProof") {
        await this.insertProof(
          message.uri,
          message.version,
          message.line,
          message.insertBlock,
          message.code
        );
        return;
      }

      if (message.command === "infoRequest") {
        console.log(`info request for clause ${message.params.clauseId}`);
        let response: InfoResponse = await this.client.sendRequest(
          "acorn/info",
          message.params
        );
        if (!response.result) {
          console.log(`info request failed: {response.failure}`);
          return;
        }
        this.panel.webview.postMessage({ type: "info", response });
        return;
      }

      if (message.command === "showLocation") {
        await this.showLocation(message.uri, message.range);
        return;
      }

      console.log("unhandled message:", message);
    } catch (e) {
      console.error("error handling webview message:", e);
    }
  }

  // Heuristically find an editor for the given uri and focus it.
  // If we don't have one open already, open a new one.
  async focusEditor(uri: string): Promise<TextEditor> {
    // Ideally we use an editor that's already visible
    for (let editor of window.visibleTextEditors) {
      if (editor.document.uri.toString() === uri) {
        await window.showTextDocument(editor.document, editor.viewColumn);
        return editor;
      }
    }

    // If the document is open but not visible, we have to guess a view column.
    for (let document of workspace.textDocuments) {
      if (document.uri.toString() === uri) {
        return window.showTextDocument(document, this.requestViewColumn);
      }
    }

    // If the document is not open, open it as a preview.
    let doc = await workspace.openTextDocument(Uri.parse(uri));
    return window.showTextDocument(doc, {
      viewColumn: this.requestViewColumn,
      preview: true,
    });
  }

  async insertAtLineStart(editor: TextEditor, line: number, text: string) {
    let success = await editor.edit((edit) => {
      // Insert the new code itself.
      let insertPos = new Position(line, 0);
      edit.insert(insertPos, text);

      // If the line before our insertion is empty, we want to delete it, so that
      // the net effect is inserting this code at the empty line.
      if (
        line > 0 &&
        editor.document.lineAt(line - 1).text.trim().length === 0
      ) {
        let prevPos = new Position(line - 1, 0);
        edit.delete(new Range(prevPos, insertPos));
      }
    });

    if (!success) {
      window.showErrorMessage("failed to insert proof");
      return;
    }

    // If the line before our insertion is empty, we want to delete it.
    if (line > 0 && editor.document.lineAt(line - 1).text.trim().length === 0) {
      let start = new Position(line - 1, 0);
      let end = new Position(line, 0);
      let success = await editor.edit((edit) => {
        edit.delete(new Range(start, end));
      });
      if (!success) {
        window.showErrorMessage("failed to delete empty line");
        return;
      }
    }
  }

  async insertAtLineEnd(editor: TextEditor, line: number, text: string) {
    let success = await editor.edit((edit) => {
      let insertPos = new Position(
        line,
        editor.document.lineAt(line).text.length
      );
      edit.insert(insertPos, text);
    });

    if (!success) {
      window.showErrorMessage("failed to insert proof");
      return;
    }
  }

  // Inserts a proof at the given line.
  // If insertBlock is true, the inserted code will be wrapped in a "by" block and inserted at
  // the end of the line.
  // If insertBlock is false, the inserted code will be inserted at the start of the line.
  // Either way, any code after the insertion will be shifted down, so that it follows
  // the inserted code.
  async insertProof(
    uri: string,
    version: number,
    line: number,
    insertBlock: boolean,
    code: string[]
  ) {
    let parts = uri.split("/");
    let filename = parts[parts.length - 1];

    let editor = await this.focusEditor(uri);
    if (!editor) {
      window.showWarningMessage(`${filename} has been closed`);
      return;
    }

    if (editor.document.version != version) {
      window.showWarningMessage(`${filename} has pending changes`);
      return;
    }

    if (line < 0 || line > editor.document.lineCount) {
      window.showErrorMessage(`invalid line number: ${line}`);
      return;
    }

    let config = workspace.getConfiguration("editor", editor.document.uri);
    let tabSize = config.get("tabSize", 4);
    let tab = " ".repeat(tabSize);
    let lineText = editor.document.lineAt(line).text;

    // Figure out how much to indent at the base level of the inserted code.
    let indentBase = "";
    for (let i = 0; i < lineText.length; i++) {
      if (lineText[i] === " ") {
        indentBase += " ";
        continue;
      }
      if (lineText[i] === "\t") {
        indentBase += tab;
        continue;
      }
      if (lineText[i] === "}" && !insertBlock) {
        // We're inserting into a block that this line closes.
        // So we want the inserted code to be more indented than this line is.
        indentBase += tab;
      }
      break;
    }

    let formatted = [];
    let indentEachLine = insertBlock ? indentBase + tab : indentBase;
    for (let c of code) {
      formatted.push(indentEachLine + c.replace(/\t/g, tab) + "\n");
    }

    if (insertBlock) {
      let text = " by {\n" + formatted.join("") + indentBase + "}";
      await this.insertAtLineEnd(editor, line, text);
    } else {
      await this.insertAtLineStart(editor, line, formatted.join(""));
    }
  }

  // Show a particular location in the codebase.
  async showLocation(uri: string, range: Range) {
    let editor = await this.focusEditor(uri);

    editor.setDecorations(showLocationDecoration, [range]);
    editor.revealRange(range, TextEditorRevealType.InCenterIfOutsideViewport);
  }

  // Show the assistant if it hasn't been shown for this workspace before, if the
  // active editor is an Acorn file.
  // Triggered by interacting with an Acorn document for the first time.
  maybeShow() {
    if (this.wasShown) {
      return;
    }
    let editor = window.activeTextEditor;
    if (!editor || editor.document.languageId !== "acorn") {
      return;
    }
    this.show(editor);
  }

  // Show the search panel itself.
  show(editor: TextEditor) {
    this.wasShown = true;
    let column =
      editor && editor.viewColumn ? editor.viewColumn + 1 : ViewColumn.Two;
    if (column === 4) {
      column = ViewColumn.Three;
    }
    if (this.panel) {
      this.panel.reveal(column);
      return;
    }
    this.panel = window.createWebviewPanel(
      "acornAssistant",
      "Acorn Assistant",
      { viewColumn: column, preserveFocus: true },
      {
        enableFindWidget: true,
        retainContextWhenHidden: true,
        enableScripts: true,
        localResourceRoots: [Uri.file(this.distPath)],
      }
    );

    this.listener = this.panel.webview.onDidReceiveMessage(
      this.handleWebviewMessage,
      this
    );

    this.panel.onDidDispose(() => {
      this.listener.dispose();
      this.listener = null;
      this.panel = null;
    });

    // Set the webview's initial content
    let distPathInWebview = this.panel.webview.asWebviewUri(
      Uri.file(this.distPath)
    );
    let indexPath = Uri.file(path.join(this.distPath, "index.html"));
    let html = fs.readFileSync(indexPath.fsPath, "utf8");
    // Inject a new base href tag
    let injected = html.replace(
      "<head>",
      `<head>\n<base href="${distPathInWebview}/">`
    );
    this.panel.webview.html = injected;

    // Always reissue the search request on panel open.
    this.chooseHelp();
    this.currentParams = null;
    this.searchOnSelection(false);
  }

  toggle(editor: TextEditor) {
    if (this.panel) {
      this.panel.dispose();
      this.panel = null;
      return;
    }

    this.show(editor);
  }

  dispose() {
    for (let subscription of this.disposables) {
      subscription.dispose();
    }
    if (this.panel) {
      this.panel.dispose();
    }
  }
}
