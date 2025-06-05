use crate::compilation::{self, ErrorSource};
use crate::names::DefinedName;
use crate::project::Project;
use crate::statement::{Statement, StatementInfo};

use super::Environment;

// This file generally contains the logic for creating an environment.
// It would be nice for the separation to be cleaner.

impl Environment {
    /// Adds a statement to the environment.
    /// If the statement has a body, this call creates a sub-environment and adds the body
    /// to that sub-environment.
    pub fn add_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
    ) -> compilation::Result<()> {
        if self.includes_explicit_false {
            return Err(
                statement.error("an explicit 'false' may not be followed by other statements")
            );
        }

        // Handle module doc collection logic before processing the statement
        if !matches!(&statement.statement, StatementInfo::DocComment(_)) {
            let current_line = statement.first_line();

            // Check if this is the first non-doc statement and there was a gap
            if self.at_module_beginning {
                if let Some(last_line) = self.last_statement_line {
                    if current_line > last_line + 1 {
                        // There was a gap between last doc comment and this statement
                        // Move accumulated doc comments to module documentation
                        self.module_doc_comments.extend(self.doc_comments.drain(..));
                    }
                }
                self.at_module_beginning = false;
            }
        }

        let result = match &statement.statement {
            StatementInfo::Type(ts) => self.add_type_statement(project, statement, ts),

            StatementInfo::Let(ls) => {
                self.add_other_lines(statement);
                self.add_let_statement(
                    project,
                    DefinedName::unqualified(self.module_id, ls.name_token.text()),
                    ls,
                    ls.name_token.range(),
                    None,
                )
            }

            StatementInfo::Define(ds) => {
                self.add_other_lines(statement);
                self.add_define_statement(
                    project,
                    DefinedName::unqualified(self.module_id, ds.name_token.text()),
                    None,
                    None,
                    ds,
                    ds.name_token.range(),
                )
            }

            StatementInfo::Theorem(ts) => self.add_theorem_statement(project, statement, ts),

            StatementInfo::Claim(cs) => self.add_claim_statement(project, statement, cs),

            StatementInfo::ForAll(fas) => self.add_forall_statement(project, statement, fas),

            StatementInfo::If(is) => self.add_if_statement(project, statement, is),

            StatementInfo::VariableSatisfy(vss) => {
                self.add_variable_satisfy_statement(project, statement, vss)
            }

            StatementInfo::FunctionSatisfy(fss) => {
                self.add_function_satisfy_statement(project, statement, fss)
            }

            StatementInfo::Structure(ss) => self.add_structure_statement(project, statement, ss),

            StatementInfo::Inductive(is) => self.add_inductive_statement(project, statement, is),

            StatementInfo::Import(is) => self.add_import_statement(project, statement, is),

            StatementInfo::Attributes(ats) => {
                self.add_attributes_statement(project, statement, ats)
            }

            StatementInfo::Numerals(ds) => self.add_numerals_statement(project, statement, ds),

            StatementInfo::Solve(ss) => self.add_solve_statement(project, statement, ss),

            StatementInfo::Problem(body) => self.add_problem_statement(project, statement, body),

            StatementInfo::Match(ms) => self.add_match_statement(project, statement, ms),

            StatementInfo::Typeclass(ts) => self.add_typeclass_statement(project, statement, ts),

            StatementInfo::Instance(is) => self.add_instance_statement(project, statement, is),

            StatementInfo::DocComment(s) => {
                let current_line = statement.first_line();

                // Check if there's a gap before this doc comment
                if self.at_module_beginning {
                    if let Some(last_line) = self.last_statement_line {
                        if current_line > last_line + 1 {
                            // There was a gap before this doc comment
                            // Move any accumulated doc comments to module documentation
                            self.module_doc_comments.extend(self.doc_comments.drain(..));
                            self.at_module_beginning = false;
                        }
                    }
                }

                self.doc_comments.push(s.clone());
                self.last_statement_line = Some(current_line);
                Ok(())
            }
        };

        // Clear doc comments after any non-doc-comment statement
        if !matches!(&statement.statement, StatementInfo::DocComment(_)) {
            self.doc_comments.clear();
            self.last_statement_line = Some(statement.first_line());
        }

        result
    }
}
