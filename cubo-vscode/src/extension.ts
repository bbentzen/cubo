//  * (c) Copyright 2026 Bruno Bentzen. All rights reserved.
//  * Released under Apache 2.0 license as described in the file LICENSE.
//  * Desc: Monitors when a .cubo file is saved, runs the compiler binary, and 
//          interprets standard OCaml error messages via regular expressions
//          to highlight lines in VS Code.
 

import * as vscode from 'vscode';
import { exec } from 'child_process';
import * as path from 'path';
import * as fs from 'fs';

let diagnosticCollection: vscode.DiagnosticCollection;

// Dictionary mapping abbreviations to Unicode symbols
const UNICODE_ABBREVIATIONS: { [key: string]: string } = {
    'to': '→',
    'lambda': 'λ',
    'let': 'λ',
    'Pi': 'Π',
    'Sigma': 'Σ',
    'times': '×',
    'vdash': '⊢',
    'nat': 'ℕ',
    'I': '𝕀',
    'eq': '≡'
};

export function activate(context: vscode.ExtensionContext) {
    diagnosticCollection = vscode.languages.createDiagnosticCollection('cubo');
    context.subscriptions.push(diagnosticCollection);

    // 1. Diagnostics on Save
    context.subscriptions.push(
        vscode.workspace.onDidSaveTextDocument((document: vscode.TextDocument) => {
            if (document.languageId === 'cubo') {
                runCuboDiagnostics(document);
            }
        })
    );

    // 2. Unicode Abbreviation Completion Provider
    const unicodeProvider = vscode.languages.registerCompletionItemProvider(
        'cubo',
        {
            provideCompletionItems(document: vscode.TextDocument, position: vscode.Position) {
                const lineText = document.lineAt(position.line).text;
                const lineStartToCursor = lineText.substring(0, position.character);
                
                // Match a backslash followed by alphanumeric characters right before the cursor
                const match = lineStartToCursor.match(/\\(\w*)$/);
                if (!match) {
                    return [];
                }

                const typedPrefix = match[1]; // e.g., "to" if they typed "\to"
                const completionItems: vscode.CompletionItem[] = [];

                // Filter and build completion suggestions based on what was typed
                for (const [abbr, symbol] of Object.entries(UNICODE_ABBREVIATIONS)) {
                    if (abbr.startsWith(typedPrefix)) {
                        const item = new vscode.CompletionItem(`\\${abbr}`, vscode.CompletionItemKind.Text);
                        item.insertText = symbol;
                        item.detail = `Unicode: ${symbol}`;
                        item.documentation = new vscode.MarkdownString(`Replaces \\\`${abbr}\\\` with \`${symbol}\``);
                        
                        // Define the specific text range to replace (including the backslash)
                        const startCharacter = position.character - (typedPrefix.length + 1);
                        item.range = new vscode.Range(
                            new vscode.Position(position.line, startCharacter),
                            position
                        );
                        
                        // Optional: Sort items so exact matches pop up first
                        item.sortText = abbr === typedPrefix ? '0' : '1' + abbr;
                        
                        completionItems.push(item);
                    }
                }

                return completionItems;
            }
        },
        '\\' // Trigger the provider automatically whenever '\' is pressed
    );

    context.subscriptions.push(unicodeProvider);
}

function runCuboDiagnostics(document: vscode.TextDocument) {
    const config = vscode.workspace.getConfiguration('cubo');
    let cuboPath = config.get<string>('executablePath') || 'cubo';

    if (cuboPath === 'cubo' && vscode.workspace.workspaceFolders) {
        const workspaceDir = vscode.workspace.workspaceFolders[0].uri.fsPath;
        const siblingCuboRoot = path.resolve(workspaceDir, '..', 'cubo');
        
        const possiblePaths = [
            path.join(siblingCuboRoot, 'cubo'),
            path.join(siblingCuboRoot, '_build', 'default', 'src', 'main.exe'),
            path.join(siblingCuboRoot, '_build', 'default', 'src', 'cubo.exe'),
            path.join(siblingCuboRoot, '_build', 'default', 'bin', 'main.exe')
        ];

        for (const p of possiblePaths) {
            if (fs.existsSync(p)) {
                cuboPath = p;
                break;
            }
        }
    }

    const filePath = document.uri.fsPath;
    diagnosticCollection.clear();

    exec(`"${cuboPath}" "${filePath}"`, (error, stdout, stderr) => {
        const output = (stdout + "\n" + stderr).trim();
        const normalizedOutput = normalizeCuboOutput(output);
        const isCommandFailure = !!error;

        if (error && ((error as any).code === 127 || error.message.includes('ENOENT'))) {
            vscode.window.showErrorMessage(
                `Cubo binary could not be located. Ensure it is compiled or set its absolute location via 'cubo.executablePath' in your VS Code settings.`
            );
            return;
        }

        if (!normalizedOutput) return;

        const locatedRegex = /line\s+(\d+),\s+characters\s+(\d+)-(\d+):([\s\S]*)/i;
        const locatedMatch = normalizedOutput.match(locatedRegex);

        if (locatedMatch) {
            const line = parseInt(locatedMatch[1], 10) - 1;
            const startChar = parseInt(locatedMatch[2], 10);
            const endChar = parseInt(locatedMatch[3], 10);
            const message = locatedMatch[4].trim();
            const diagnosticMessage = /unexpected token variant/i.test(message)
                ? `Syntax Error:\n${message}`
                : message;

            createDiagnostic(document, line, startChar, endChar, diagnosticMessage, vscode.DiagnosticSeverity.Error);
            return;
        }

        const genericLineRegex = /(?:line|line:)\s+(\d+)/i;
        const lineMatch = normalizedOutput.match(genericLineRegex);

        if (lineMatch) {
            const line = parseInt(lineMatch[1], 10) - 1;
            const lineText = document.lineAt(line).text;
            createDiagnostic(document, line, 0, lineText.length, normalizedOutput, vscode.DiagnosticSeverity.Error);
            return;
        }

        createDiagnostic(
            document,
            0,
            0,
            10,
            isCommandFailure ? `Cubo Error:\n${normalizedOutput}` : `Cubo Output:\n${normalizedOutput}`,
            isCommandFailure ? vscode.DiagnosticSeverity.Error : vscode.DiagnosticSeverity.Information
        );
    });
}

function normalizeCuboOutput(output: string): string {
    const failurePrefix = 'Fatal error: exception Failure("';

    if (output.startsWith(failurePrefix) && output.endsWith('")')) {
        const escaped = output.slice(failurePrefix.length, -2);
        return escaped
            .replace(/\\n/g, '\n')
            .replace(/\\r/g, '\r')
            .replace(/\\t/g, '\t')
            .replace(/\\"/g, '"')
            .replace(/\\\\/g, '\\');
    }

    return output;
}

function createDiagnostic(document: vscode.TextDocument, line: number, start: number, end: number, message: string, severity: vscode.DiagnosticSeverity) {
    const safeLine = Math.min(Math.max(0, line), document.lineCount - 1);
    const lineText = document.lineAt(safeLine).text;
    const safeEnd = Math.min(end, lineText.length);

    const range = new vscode.Range(
        new vscode.Position(safeLine, start),
        new vscode.Position(safeLine, safeEnd)
    );

    const diagnostic = new vscode.Diagnostic(
        range,
        message,
        severity
    );

    diagnosticCollection.set(document.uri, [diagnostic]);
}

export function deactivate() {}