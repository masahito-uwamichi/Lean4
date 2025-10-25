# Lean4 Podman環境

このディレクトリには、PodmanでLean4開発環境を構築するための設定ファイルが含まれています。

## 必要な要件

- Podman (4.0以降推奨)
- podman-compose (オプション、推奨)

### Podmanのインストール

#### Windows
1. [Podman公式サイト](https://podman.io/getting-started/installation)からWindows版をダウンロード
2. インストーラーを実行してインストール

#### macOS
```bash
brew install podman
```

#### Ubuntu/Debian
```bash
sudo apt-get update
sudo apt-get install podman
```

#### CentOS/RHEL/Fedora
```bash
sudo dnf install podman
```

### podman-composeのインストール（推奨）
```bash
pip3 install podman-compose
```

## ファイル構成

```
environments/lean4/
├── Dockerfile              # Lean4開発環境のコンテナイメージ定義
├── docker-compose.yml      # Podman Composeサービス定義
├── lean4-podman.sh         # Linux/macOS用管理スクリプト
├── lean4-podman.cmd        # Windows用管理スクリプト
└── README.md              # このファイル
```

## 使用方法

### 1. 環境の準備

プロジェクトのルートディレクトリで以下を実行：

#### Linux/macOS
```bash
# スクリプトに実行権限を付与
chmod +x environments/lean4/lean4-podman.sh

# environments/lean4ディレクトリに移動
cd environments/lean4
```

#### Windows
```cmd
# environments/lean4ディレクトリに移動
cd environments\lean4
```

### 2. 基本的な使用手順

#### Linux/macOS
```bash
# 1. Lean4イメージをビルド
./lean4-podman.sh build

# 2. コンテナを起動
./lean4-podman.sh start

# 3. コンテナに接続して開発開始
./lean4-podman.sh exec

# 4. 開発終了後、コンテナを停止
./lean4-podman.sh stop
```

#### Windows
```cmd
# 1. Lean4イメージをビルド
lean4-podman.cmd build

# 2. コンテナを起動
lean4-podman.cmd start

# 3. コンテナに接続して開発開始
lean4-podman.cmd exec

# 4. 開発終了後、コンテナを停止
lean4-podman.cmd stop
```

### 3. コンテナ内での作業

コンテナに接続すると、`/workspace`ディレクトリにプロジェクトがマウントされています。

```bash
# Lean4のバージョン確認
lean --version

# Lakeのバージョン確認
lake --version

# 新しいLean4プロジェクトを作成
lake new MyProject
cd MyProject

# プロジェクトをビルド
lake build

# REPLを起動
lake exe repl
```

## 管理スクリプトのコマンド

### 利用可能なコマンド

- `build` - Lean4 Dockerイメージをビルド
- `start` - Lean4コンテナを起動
- `stop` - Lean4コンテナを停止
- `exec` - 実行中のコンテナに接続
- `status` - 環境の状態を確認
- `clean` - すべてのコンテナとイメージを削除
- `help` - ヘルプメッセージを表示

### 例

```bash
# 環境の状態確認
./lean4-podman.sh status

# すべてのリソースをクリーンアップ
./lean4-podman.sh clean
```

## コンテナの詳細

### 含まれているソフトウェア

- Ubuntu 22.04ベース
- Lean4 v4.12.0
- Lake (Lean package manager)
- Git
- Python3
- 必要な開発ツール（gcc, cmake, etc.）

### ポート設定

- `8080`: Lean Language Serverやその他のサービス用（必要に応じて調整）

### ボリュームマウント

- プロジェクトディレクトリ: `/workspace`
- Lean4キャッシュ: `lean4-cache`ボリューム
- Elanデータ: `lean4-elan`ボリューム

### ユーザー設定

- ユーザー名: `lean`
- UID/GID: 1000:1000

## トラブルシューティング

### 権限エラーが発生する場合

Linux環境でファイル権限の問題が発生した場合：

```bash
# プロジェクトディレクトリの権限を調整
sudo chown -R $(id -u):$(id -g) .
```

### SELinuxエラーが発生する場合

SELinuxが有効な環境では、ボリュームマウントに`:Z`フラグが必要です（docker-compose.ymlに含まれています）。

### Podmanが見つからない場合

```bash
# Podmanがインストールされているか確認
which podman

# Podmanのバージョン確認
podman version
```

### メモリ不足エラーが発生する場合

コンテナのメモリ制限を調整：

```bash
# docker-compose.ymlに以下を追加
deploy:
  resources:
    limits:
      memory: 4G
```

## より高度な使用方法

### カスタムLean4バージョンの使用

`Dockerfile`の`LEAN_VERSION`環境変数を変更してリビルド：

```dockerfile
ENV LEAN_VERSION=v4.11.0
```

### 追加パッケージのインストール

`Dockerfile`を編集して必要なパッケージを追加：

```dockerfile
RUN apt-get update && apt-get install -y \
    your-additional-package \
    && rm -rf /var/lib/apt/lists/*
```

### ネットワーク設定のカスタマイズ

必要に応じて`docker-compose.yml`のネットワーク設定を調整できます。

## 参考リンク

- [Lean4公式ドキュメント](https://lean-lang.org/lean4/doc/)
- [Podman公式ドキュメント](https://docs.podman.io/)
- [Lake (Lean Package Manager)](https://github.com/leanprover/lake)
- [Elan (Lean Toolchain Manager)](https://github.com/leanprover/elan)