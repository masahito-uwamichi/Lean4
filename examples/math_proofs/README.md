# Lean4 数学的証明サンプル

このディレクトリには、Lean4で記述された数学的証明のサンプルが含まれています。PDF出力機能のデモンストレーションとしても使用できます。

## プロジェクト構成

```
examples/math_proofs/
├── MathProofs.lean      # メインの証明ファイル
├── lakefile.lean        # Lake設定ファイル
├── lean-toolchain      # Lean4バージョン指定
└── README.md           # このファイル
```

## 含まれている証明

### 1. 自然数の基本性質
- 加法の単位元性質（n + 0 = n, 0 + n = n）
- 加法の交換律（m + n = n + m）
- 加法の結合律（(l + m) + n = l + (m + n)）

### 2. 実数の性質
- 加法単位元（x + 0 = x）
- 乗法単位元（x * 1 = x）
- 分配律（a * (b + c) = a * b + a * c）
- 平方の非負性（0 ≤ x²）

### 3. 不等式の性質
- 三角不等式（|x + y| ≤ |x| + |y|）
- 算術・幾何平均の不等式（AM-GM）

### 4. 組み合わせ論
- 鳩の巣原理の簡単なバージョン

### 5. 数列の性質
- フィボナッチ数列の定義
- フィボナッチ数列の基本性質
- フィボナッチ数列の正の性質

## 使用方法

### 1. 環境の準備

Podmanコンテナ内で作業することを前提としています：

```bash
# コンテナを起動（プロジェクトルートから）
cd environments/lean4
./lean4-podman.sh start
./lean4-podman.sh exec
```

### 2. プロジェクトのセットアップ

```bash
# examples/math_proofsディレクトリに移動
cd examples/math_proofs

# 依存関係の取得（初回のみ）
lake exe cache get

# プロジェクトのビルド
lake build
```

### 3. 証明の検証

```bash
# Lean4ファイルをチェック
lean MathProofs.lean

# 対話的にREPLで確認
lake exe repl
```

### 4. PDF生成

```bash
# PDFを生成（出力ディレクトリを指定）
../../environments/lean4/generate-pdf.sh MathProofs.lean ./output

# 生成されたファイルを確認
ls -la output/
# MathProofs.html  - HTML版
# MathProofs.tex   - LaTeX版
# MathProofs.pdf   - PDF版
```

## Lean4の証明例の解説

### 基本的な証明戦術

このサンプルでは以下の証明戦術を使用しています：

- `rw` (rewrite): 定義や定理を使った書き換え
- `linarith`: 線形算術の自動証明
- `exact`: 正確な項の提供
- `constructor`: 構造の構築
- `cases`: 場合分けによる証明
- `sorry`: 証明の省略（実装予定箇所）

### 証明の構造

```lean
/-- **定理**: 定理の説明 -/
theorem theorem_name (variables : Types) (hypotheses : Conditions) : 
    conclusion := by
  proof_tactics
```

### ドキュメンテーション

- `/-- ... -/`: ドキュメンテーションコメント
- `-- `: 行コメント
- `/-! ... -/`: セクションドキュメント

## カスタマイズ

### 新しい証明の追加

1. `MathProofs.lean`に新しい定理を追加
2. 適切な`import`文を追加（必要に応じて）
3. ドキュメンテーションコメントを記述
4. 証明を実装

### 依存関係の追加

`lakefile.lean`でMathlib以外のライブラリを追加：

```lean
require «library_name» from git
  "https://github.com/user/repo.git"
```

## 学習リソース

### Lean4の学習

- [Lean4マニュアル](https://lean-lang.org/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)

### Mathlibの使用

- [Mathlib4ドキュメント](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathlibの戦術一覧](https://leanprover-community.github.io/mathlib4_docs/tactics.html)

### PDF生成について

- [Alectryonドキュメント](https://github.com/cpitclaudel/alectryon)
- [LaTeX数式の書き方](https://en.wikibooks.org/wiki/LaTeX/Mathematics)

## よくある問題

### ビルドエラー

```bash
# キャッシュをクリア
lake clean
lake build

# 依存関係を再取得
lake exe cache get
```

### 証明エラー

- `#check` コマンドで型を確認
- `sorry` を使って部分的に証明を構築
- LSP（Language Server Protocol）を活用してエラーメッセージを確認

### PDF生成エラー

- Lean4ファイルがビルドできることを確認
- `alectryon --version` でツールの動作確認
- LaTeXログファイル（`.log`）を確認