#!/bin/bash

# Lean4 PDF生成スクリプト
# Lean4のコメントと証明を解析してLaTeX/PDFを生成

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

# カラー出力の設定
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# ログ関数（POSIX互換）
log_info() {
    printf "${BLUE}[INFO]${NC} %s\n" "$1"
}

log_success() {
    printf "${GREEN}[SUCCESS]${NC} %s\n" "$1"
}

log_warning() {
    printf "${YELLOW}[WARNING]${NC} %s\n" "$1"
}

log_error() {
    printf "${RED}[ERROR]${NC} %s\n" "$1"
}

# 使用方法の表示
show_help() {
    echo "Lean4 PDF生成スクリプト"
    echo ""
    echo "使用方法:"
    echo "  $0 <lean_file> [output_dir]"
    echo ""
    echo "引数:"
    echo "  lean_file   - 変換するLean4ファイル(.lean)"
    echo "  output_dir  - 出力ディレクトリ（省略時はカレントディレクトリ）"
    echo ""
    echo "例:"
    echo "  $0 MathProofs.lean"
    echo "  $0 MathProofs.lean ./output"
    echo ""
    echo "このスクリプトは以下を生成します:"
    echo "  - HTML版ドキュメント"
    echo "  - LaTeX版ドキュメント"
    echo "  - PDF版ドキュメント"
}

# 必要なツールの確認
check_dependencies() {
    log_info "依存関係を確認しています..."
    
    # LaTeXの確認
    if ! command -v pdflatex >/dev/null 2>&1; then
        log_error "pdflatexがインストールされていません"
        log_info "TeXLiveをインストールしてください"
        exit 1
    fi
    
    # Leanの確認
    if ! command -v lean >/dev/null 2>&1; then
        log_error "Lean4がインストールされていません"
        exit 1
    fi
    
    # Pythonの確認
    if ! command -v python3 >/dev/null 2>&1; then
        log_error "Python3がインストールされていません"
        exit 1
    fi
    
    log_success "すべての依存関係が確認できました"
}

# シンプルなPDFを生成する関数

# PDFを生成する関数
generate_pdf() {
    local lean_file="$1"
    local output_dir="$2"
    local base_name
    base_name=$(basename "$lean_file" .lean)
    
    log_info "Lean4ファイルを処理しています: $lean_file"
    
    # 出力ディレクトリの作成
    mkdir -p "$output_dir"
    
    # シンプルなパーサーをコピー
    local parser_file="$output_dir/lean_parser.py"
    cp "$SCRIPT_DIR/simple_lean_parser.py" "$parser_file"
    
    # 1. Lean4ファイルをLaTeXに変換
    log_info "Lean4ファイルをLaTeXに変換しています..."
    local content_tex="$output_dir/${base_name}_content.tex"
    
    if python3 "$parser_file" "$lean_file" "$content_tex"; then
        log_success "LaTeX変換が完了しました"
    else
        log_error "LaTeX変換に失敗しました"
        return 1
    fi
    
    # 2. 完全なLaTeXドキュメントを生成
    log_info "完全なLaTeXドキュメントを生成しています..."
    create_enhanced_latex "$content_tex" "$output_dir/${base_name}.tex"
    
    # 3. PDFを生成
    log_info "PDFを生成しています..."
    original_dir=$(pwd)
    cd "$output_dir"
    
    # PDFLaTeXでコンパイル（複数回実行してクロスリファレンスを解決）
    pdflatex -interaction=nonstopmode "${base_name}.tex" >/dev/null 2>&1
    latex_exit_code=$?
    pdflatex -interaction=nonstopmode "${base_name}.tex" >/dev/null 2>&1
    second_exit_code=$?
    
    # PDFファイルの生成確認
    if [ -f "${base_name}.pdf" ] && [ -s "${base_name}.pdf" ]; then
        # ファイルサイズを取得（より互換性のある方法）
        pdf_size=$(wc -c < "${base_name}.pdf" 2>/dev/null || echo "0")
        if [ "$pdf_size" -gt 1000 ]; then  # 1KB以上のPDFファイルが生成されているか確認
            log_success "PDFファイルが生成されました: ${output_dir}/${base_name}.pdf"
            log_info "PDFファイルサイズ: $(du -h "${base_name}.pdf" 2>/dev/null | cut -f1 || echo 'N/A')"
            pdf_generated=true
        else
            log_error "PDFファイルは生成されましたが、サイズが小さすぎます ($pdf_size bytes)"
            pdf_generated=false
        fi
    else
        log_error "PDFファイルの生成に失敗しました"
        log_warning "LaTeXのログファイルを確認してください: ${base_name}.log"
        if [ "$latex_exit_code" -ne 0 ]; then
            log_warning "最初のLaTeX実行の終了コード: $latex_exit_code"
        fi
        if [ "$second_exit_code" -ne 0 ]; then
            log_warning "2回目のLaTeX実行の終了コード: $second_exit_code"
        fi
        pdf_generated=false
    fi
    
    # 4. HTMLバージョンも生成（pandocを使用）
    log_info "HTMLバージョンを生成しています..."
    if command -v pandoc >/dev/null 2>&1; then
        pandoc -f latex -t html5 --standalone --mathjax \
               --metadata title="Lean4 Mathematical Proofs" \
               "${base_name}.tex" -o "${base_name}.html" 2>/dev/null
        if [ -f "${base_name}.html" ]; then
            log_success "HTMLファイルが生成されました: ${output_dir}/${base_name}.html"
        fi
    else
        log_warning "pandocがインストールされていません。HTMLファイルは生成されません。"
    fi
    
    # 一時ファイルのクリーンアップ
    rm -f *.aux *.log *.out *.toc "$parser_file" "${base_name}_content.tex"
    
    cd "$original_dir"
    
    # 成功判定
    if [ "$pdf_generated" = "true" ]; then
        return 0
    else
        return 1
    fi
}

# 拡張LaTeXファイルを作成する関数
create_enhanced_latex() {
    local content_file="$1"
    local output_file="$2"
    
    cat > "$output_file" << 'EOF'
\documentclass[12pt,a4paper]{article}
\usepackage[utf8]{inputenc}
\usepackage[japanese]{babel}
\usepackage{CJKutf8}
\usepackage{amsmath,amsfonts,amssymb,amsthm}
\usepackage{geometry}
\usepackage{fancyhdr}
\usepackage{hyperref}
\usepackage{xcolor}
\usepackage{listings}
\usepackage{tcolorbox}
\usepackage{mdframed}

% ページ設定
\geometry{margin=2.5cm}
\setlength{\headheight}{15pt}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{Lean4 Mathematical Proofs}
\fancyhead[R]{\thepage}

% 色の定義
\definecolor{leanblue}{RGB}{0,102,204}
\definecolor{lightgray}{RGB}{248,248,248}

% Lean4コードのスタイル設定
\lstdefinestyle{lean}{
  backgroundcolor=\color{lightgray},
  basicstyle=\ttfamily\small,
  keywordstyle=\color{leanblue}\bfseries,
  commentstyle=\color{gray},
  stringstyle=\color{red},
  numberstyle=\tiny\color{gray},
  numbers=left,
  frame=single,
  breaklines=true,
  breakatwhitespace=true,
  showspaces=false,
  showstringspaces=false,
  tabsize=2
}

% 定理環境の設定
\theoremstyle{definition}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{example}[theorem]{Example}

% タイトル
\title{Lean4 Mathematical Proofs\\
       \large Formalized Mathematics Examples}
\author{Lean4 Project}
\date{\today}

\begin{document}
\begin{CJK}{UTF8}{min}
\maketitle
\tableofcontents
\newpage

EOF

    # 変換されたコンテンツを追加
    if [ -f "$content_file" ]; then
        cat "$content_file" >> "$output_file"
    fi
    
    cat >> "$output_file" << 'EOF'

\end{CJK}
\end{document}
EOF
}

# メイン処理
main() {
    if [ $# -lt 1 ] || [ "$1" = "--help" ] || [ "$1" = "-h" ]; then
        show_help
        exit 0
    fi
    
    local lean_file="$1"
    local output_dir="${2:-.}"
    
    # ファイルの存在確認
    if [ ! -f "$lean_file" ]; then
        log_error "ファイルが見つかりません: $lean_file"
        exit 1
    fi
    
    # 拡張子の確認
    case "$lean_file" in
        *.lean) ;;
        *) log_error "Lean4ファイル(.lean)を指定してください"; exit 1 ;;
    esac
    
    check_dependencies
    generate_pdf "$lean_file" "$output_dir"
    
    log_success "PDF生成が完了しました！"
}

main "$@"