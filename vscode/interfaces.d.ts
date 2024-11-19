// Interfaces with the language server.
// This should be kept parallel to interfaces.rs.

interface DocumentProgress {
  version: number;
  verified: [number, number][];
}

interface ProgressResponse {
  buildId: number | null;
  done: number;
  total: number;
  docs: { [url: string]: DocumentProgress };
}

interface SearchParams {
  uri: string;
  version: number;
  selectedLine: number;
  id: number;
}

interface Position {
  line: number;
  character: number;
}

interface Range {
  start: Position;
  end: Position;
}

interface Location {
  uri: string;
  range: Range;
}

interface ClauseInfo {
  text: string | null;
  id: number | null;
}

interface ProofStepInfo {
  clause: ClauseInfo;
  premises: Array<[String, ClauseInfo]>;
  rule: string;
  location: Location | null;
  depth: number;
}

interface SearchStatus {
  code: Array<string> | null;
  codeError: string | null;
  steps: Array<ProofStepInfo> | null;
  outcome: string | null;
  needsSimplification: boolean | null;
  numActivated: number;
}

interface SearchResponse {
  uri: string;
  version: number;
  failure: string | null;
  loading: boolean;
  goalName: string | null;
  goalRange: Range | null;
  proofInsertionLine: number;
  insertBlock: boolean;
  status: SearchStatus;
  id: number;
}

interface InfoParams {
  searchId: number;
  clauseId: number;
}

interface InfoResult {
  clause: ClauseInfo;
  step: ProofStepInfo;
  consequences: Array<ProofStepInfo>;
  numConsequences: number;
}

interface InfoResponse {
  searchId: number;
  failure: string | null;
  result: InfoResult | null;
}

// This section is for the extension to communicate with the assistant.
// There's no Rust equivalent for these interfaces.

// Sent from the extension to the assistant to indicate that the user might need help, and they haven't
// saved an active Acorn document yet so we can't give them very specific help on it.
// If none of the flags are set, that clears any presave help.
interface PreSaveHelp {
  // We don't even have an Acorn file to do anything with.
  noFile?: boolean;

  // The user has just created a new document, so they might need to know how to get started.
  newDocument?: boolean;
}
