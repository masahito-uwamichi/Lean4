#!/usr/bin/env python3
"""
Lean4ファイルから基本的なLaTeXドキュメントを生成するシンプルなスクリプト
"""

import re
import sys
import os

def escape_latex(text):
    """LaTeX特殊文字をエスケープする"""
    replacements = {
        '\\': '\\textbackslash{}',
        '{': '\\{',
        '}': '\\}',
        '$': '\\$',
        '&': '\\&',
        '%': '\\%',
        '#': '\\#',
        '^': '\\textasciicircum{}',
        '_': '\\_',
        '~': '\\textasciitilde{}',
        'ℕ': '\\mathbb{N}',
        'ℝ': '\\mathbb{R}',
        'ℤ': '\\mathbb{Z}',
        'ℚ': '\\mathbb{Q}',
        '≤': '\\leq',
        '≥': '\\geq',
        '→': '\\to',
        '∀': '\\forall',
        '∃': '\\exists',
        '∧': '\\land',
        '∨': '\\lor',
        '¬': '\\lnot'
    }
    
    result = text
    for char, replacement in replacements.items():
        result = result.replace(char, replacement)
    return result

def process_lean_file(file_path):
    """Lean4ファイルを読み込んで処理する"""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    lines = content.split('\n')
    latex_content = []
    
    in_doc_comment = False
    current_section = 0
    
    for line in lines:
        stripped = line.strip()
        
        # 空行をスキップ
        if not stripped:
            latex_content.append('')
            continue
        
        # ドキュメントコメントの開始
        if stripped.startswith('/-!'):
            in_doc_comment = True
            continue
        
        # ドキュメントコメントの終了
        if stripped.endswith('-/') and in_doc_comment:
            in_doc_comment = False
            continue
        
        # ドキュメントコメント内の処理
        if in_doc_comment:
            # セクション見出しを検出
            if stripped.startswith('#'):
                level = len(stripped) - len(stripped.lstrip('#'))
                title = stripped.lstrip('#').strip()
                
                if level == 1:
                    latex_content.append(f'\\section{{{escape_latex(title)}}}')
                elif level == 2:
                    latex_content.append(f'\\subsection{{{escape_latex(title)}}}')
                else:
                    latex_content.append(f'\\subsubsection{{{escape_latex(title)}}}')
            else:
                # 通常のドキュメントテキスト
                if stripped and not stripped.startswith('-'):
                    latex_content.append(escape_latex(stripped))
            continue
        
        # インポート文をスキップ
        if stripped.startswith('import '):
            continue
        
        # 名前空間をスキップ
        if stripped.startswith('namespace ') or stripped == 'end MathProofs':
            continue
        
        # 定理の処理
        theorem_match = re.match(r'/--\s*\*\*([^*]+)\*\*[^-]*-/', stripped)
        if theorem_match:
            theorem_title = theorem_match.group(1).strip()
            latex_content.append(f'\\begin{{theorem}}[{escape_latex(theorem_title)}]')
            continue
        
        # theorem定義の処理
        if stripped.startswith('theorem '):
            # 定理の内容を抽出
            theorem_content = stripped[8:].strip()  # "theorem "を削除
            
            # 定理名を抽出
            name_match = re.match(r'(\w+)', theorem_content)
            if name_match:
                theorem_name = name_match.group(1)
                
                # 残りの部分を処理
                rest = theorem_content[len(theorem_name):].strip()
                if rest.startswith('(') and ':' in rest:
                    # パラメータと型の分離
                    colon_pos = rest.find(':')
                    params = rest[1:colon_pos].rstrip(')')
                    statement = rest[colon_pos+1:].strip()
                    
                    latex_content.append(f'For {escape_latex(params)}, we have:')
                    latex_content.append(f'\\[ {escape_latex(statement.replace(" := by", "").replace(" by", ""))} \\]')
                else:
                    latex_content.append(f'\\texttt{{{escape_latex(theorem_content)}}}')
            continue
        
        # 証明戦術の処理
        if stripped in ['by', 'by simp', 'by rw', 'by exact', 'by linarith', 'sorry']:
            latex_content.append('\\begin{proof}')
            if stripped != 'by':
                latex_content.append(f'Using: \\texttt{{{escape_latex(stripped)}}}')
            latex_content.append('\\end{proof}')
            latex_content.append('\\end{theorem}')
            latex_content.append('')
            continue
        
        # より複雑な証明戦術
        if re.match(r'\s*(rw|simp|exact|linarith|cases|constructor|sorry)', stripped):
            latex_content.append('\\begin{proof}')
            latex_content.append(f'Using: \\texttt{{{escape_latex(stripped)}}}')
            latex_content.append('\\end{proof}')
            latex_content.append('\\end{theorem}')
            latex_content.append('')
            continue
        
        # 定義の処理
        if stripped.startswith('def '):
            def_content = stripped[4:].strip()
            latex_content.append(f'\\begin{{definition}}')
            latex_content.append(f'\\texttt{{{escape_latex(def_content)}}}')
            latex_content.append('\\end{definition}')
            latex_content.append('')
            continue
    
    return '\n'.join(latex_content)

def main():
    if len(sys.argv) != 3:
        print("Usage: python3 lean_parser.py <input_file> <output_file>")
        sys.exit(1)
    
    input_file, output_file = sys.argv[1], sys.argv[2]
    
    if not os.path.exists(input_file):
        print(f"Error: Input file {input_file} does not exist")
        sys.exit(1)
    
    try:
        latex_content = process_lean_file(input_file)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(latex_content)
        
        print(f"Successfully converted {input_file} to {output_file}")
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == '__main__':
    main()