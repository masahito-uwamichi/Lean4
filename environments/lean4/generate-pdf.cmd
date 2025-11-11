@echo off
setlocal enabledelayedexpansion

REM Lean4 PDF生成スクリプト (Windows版)
REM alectryonを使用してLean4ファイルからPDFを生成

set "SCRIPT_DIR=%~dp0"

REM カラー出力の設定
set "RED=[91m"
set "GREEN=[92m"
set "YELLOW=[93m"
set "BLUE=[94m"
set "NC=[0m"

if "%1"=="" goto :help
if "%1"=="--help" goto :help
if "%1"=="-h" goto :help

set "LEAN_FILE=%1"
set "OUTPUT_DIR=%2"
if "%OUTPUT_DIR%"=="" set "OUTPUT_DIR=."

REM ファイルの存在確認
if not exist "%LEAN_FILE%" (
    echo %RED%[ERROR]%NC% ファイルが見つかりません: %LEAN_FILE%
    exit /b 1
)

REM 拡張子の確認
echo %LEAN_FILE% | findstr /e ".lean" >nul
if errorlevel 1 (
    echo %RED%[ERROR]%NC% Lean4ファイル(.lean)を指定してください
    exit /b 1
)

call :check_dependencies
if errorlevel 1 exit /b 1

call :generate_pdf "%LEAN_FILE%" "%OUTPUT_DIR%"
if errorlevel 1 exit /b 1

echo %GREEN%[SUCCESS]%NC% PDF生成が完了しました！
goto :eof

:check_dependencies
echo %BLUE%[INFO]%NC% 依存関係を確認しています...

REM alectryonの確認
where alectryon >nul 2>&1
if errorlevel 1 (
    echo %RED%[ERROR]%NC% alectryonがインストールされていません
    echo %BLUE%[INFO]%NC% 以下のコマンドでインストールしてください:
    echo %BLUE%[INFO]%NC%   pip install alectryon[lean4]
    exit /b 1
)

REM LaTeXの確認
where pdflatex >nul 2>&1
if errorlevel 1 (
    echo %RED%[ERROR]%NC% pdflatexがインストールされていません
    echo %BLUE%[INFO]%NC% TeXLiveをインストールしてください
    exit /b 1
)

REM Leanの確認
where lean >nul 2>&1
if errorlevel 1 (
    echo %RED%[ERROR]%NC% Lean4がインストールされていません
    exit /b 1
)

echo %GREEN%[SUCCESS]%NC% すべての依存関係が確認できました
goto :eof

:generate_pdf
set "LEAN_FILE=%~1"
set "OUTPUT_DIR=%~2"

for %%F in ("%LEAN_FILE%") do set "BASE_NAME=%%~nF"

echo %BLUE%[INFO]%NC% Lean4ファイルを処理しています: %LEAN_FILE%

REM 出力ディレクトリの作成
if not exist "%OUTPUT_DIR%" mkdir "%OUTPUT_DIR%"

REM 1. HTMLバージョンを生成
echo %BLUE%[INFO]%NC% HTMLバージョンを生成しています...
alectryon --frontend lean4 "%LEAN_FILE%" --output-directory "%OUTPUT_DIR%" --output "%BASE_NAME%.html"
if errorlevel 1 (
    echo %RED%[ERROR]%NC% HTMLファイルの生成に失敗しました
    exit /b 1
)
echo %GREEN%[SUCCESS]%NC% HTMLファイルが生成されました: %OUTPUT_DIR%\%BASE_NAME%.html

REM 2. LaTeXバージョンを生成
echo %BLUE%[INFO]%NC% LaTeXバージョンを生成しています...
alectryon --frontend lean4 "%LEAN_FILE%" --backend latex --output-directory "%OUTPUT_DIR%" --output "%BASE_NAME%.tex"
if errorlevel 1 (
    echo %RED%[ERROR]%NC% LaTeXファイルの生成に失敗しました
    exit /b 1
)
echo %GREEN%[SUCCESS]%NC% LaTeXファイルが生成されました: %OUTPUT_DIR%\%BASE_NAME%.tex

REM 3. PDFを生成
echo %BLUE%[INFO]%NC% PDFを生成しています...
cd /d "%OUTPUT_DIR%"

REM 拡張LaTeXファイルを作成
call :create_enhanced_latex "%BASE_NAME%.tex" "%BASE_NAME%_enhanced.tex"

REM PDFLaTeXでコンパイル
pdflatex -interaction=nonstopmode "%BASE_NAME%_enhanced.tex" >nul 2>&1
pdflatex -interaction=nonstopmode "%BASE_NAME%_enhanced.tex" >nul 2>&1

if exist "%BASE_NAME%_enhanced.pdf" (
    move "%BASE_NAME%_enhanced.pdf" "%BASE_NAME%.pdf" >nul
    echo %GREEN%[SUCCESS]%NC% PDFファイルが生成されました: %OUTPUT_DIR%\%BASE_NAME%.pdf
) else (
    echo %RED%[ERROR]%NC% PDFファイルの生成に失敗しました
    echo %YELLOW%[WARNING]%NC% LaTeXのログファイルを確認してください: %BASE_NAME%_enhanced.log
    exit /b 1
)

REM 一時ファイルのクリーンアップ
del /q *.aux *.log *.out *.toc "%BASE_NAME%_enhanced.tex" 2>nul

cd /d "%SCRIPT_DIR%"
goto :eof

:create_enhanced_latex
set "INPUT_FILE=%~1"
set "OUTPUT_FILE=%~2"

(
echo \documentclass[12pt,a4paper]{article}
echo \usepackage[utf8]{inputenc}
echo \usepackage[T1]{fontenc}
echo \usepackage{amsmath,amsfonts,amssymb,amsthm}
echo \usepackage{geometry}
echo \usepackage{fancyhdr}
echo \usepackage{hyperref}
echo \usepackage{xcolor}
echo \usepackage{listings}
echo \usepackage{tcolorbox}
echo \usepackage{mdframed}
echo.
echo %% ページ設定
echo \geometry{margin=2.5cm}
echo \pagestyle{fancy}
echo \fancyhf{}
echo \fancyhead[L]{Lean4 数学的証明}
echo \fancyhead[R]{\thepage}
echo.
echo %% 色の定義
echo \definecolor{leanblue}{RGB}{0,102,204}
echo \definecolor{lightgray}{RGB}{248,248,248}
echo.
echo %% Lean4コードのスタイル設定
echo \lstdefinestyle{lean}{
echo   backgroundcolor=\color{lightgray},
echo   basicstyle=\ttfamily\small,
echo   keywordstyle=\color{leanblue}\bfseries,
echo   commentstyle=\color{gray},
echo   stringstyle=\color{red},
echo   numberstyle=\tiny\color{gray},
echo   numbers=left,
echo   frame=single,
echo   breaklines=true,
echo   breakatwhitespace=true,
echo   showspaces=false,
echo   showstringspaces=false,
echo   tabsize=2
echo }
echo.
echo %% 定理環境の設定
echo \theoremstyle{definition}
echo \newtheorem{theorem}{定理}[section]
echo \newtheorem{lemma}[theorem]{補題}
echo \newtheorem{definition}[theorem]{定義}
echo \newtheorem{example}[theorem]{例}
echo.
echo %% タイトル
echo \title{Lean4による数学的証明\\
echo        \large 形式化された数学の例}
echo \author{Lean4プロジェクト}
echo \date{\today}
echo.
echo \begin{document}
echo \maketitle
echo \tableofcontents
echo \newpage
echo.
) > "%OUTPUT_FILE%"

REM 元のLaTeXファイルの内容を追加（簡略版）
if exist "%INPUT_FILE%" (
    type "%INPUT_FILE%" >> "%OUTPUT_FILE%"
)

echo. >> "%OUTPUT_FILE%"
echo \end{document} >> "%OUTPUT_FILE%"

goto :eof

:help
echo Lean4 PDF生成スクリプト
echo.
echo 使用方法:
echo   %~nx0 ^<lean_file^> [output_dir]
echo.
echo 引数:
echo   lean_file   - 変換するLean4ファイル(.lean)
echo   output_dir  - 出力ディレクトリ（省略時はカレントディレクトリ）
echo.
echo 例:
echo   %~nx0 MathProofs.lean
echo   %~nx0 MathProofs.lean .\output
echo.
echo このスクリプトは以下を生成します:
echo   - HTML版ドキュメント
echo   - LaTeX版ドキュメント
echo   - PDF版ドキュメント
goto :eof