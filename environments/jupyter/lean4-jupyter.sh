#!/bin/bash

# Lean4 Jupyter環境管理スクリプト

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
PROJECT_ROOT="$(dirname "$(dirname "$SCRIPT_DIR")")"

# カラー出力の設定
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# ログ関数
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

# Podmanの確認
check_podman() {
    if ! command -v podman &> /dev/null; then
        log_error "Podmanがインストールされていません"
        log_info "以下のコマンドでインストールしてください:"
        log_info "  Ubuntu/Debian: sudo apt-get install podman"
        log_info "  CentOS/RHEL: sudo dnf install podman"
        log_info "  macOS: brew install podman"
        exit 1
    fi
    
    if ! command -v podman-compose &> /dev/null; then
        log_warning "podman-composeがインストールされていません"
        log_info "以下のコマンドでインストールしてください:"
        log_info "  pip3 install podman-compose"
    fi
}

# イメージをビルド
build() {
    log_info "Lean4 Jupyter環境をビルドしています..."
    cd "$SCRIPT_DIR"
    
    if command -v podman-compose &> /dev/null; then
        podman-compose build
    else
        podman build -t lean4-jupyter:latest .
    fi
    
    log_success "イメージのビルドが完了しました"
}

# コンテナを起動
start() {
    log_info "Lean4 Jupyterコンテナを起動しています..."
    cd "$SCRIPT_DIR"
    
    if command -v podman-compose &> /dev/null; then
        podman-compose up -d
    else
        podman run -d \
            --name lean4-jupyter-container \
            -p 8888:8888 \
            -v "$PROJECT_ROOT:/workspace:Z" \
            -v lean4-jupyter-config:/home/lean/.jupyter \
            -v lean4-jupyter-notebooks:/home/lean/notebooks \
            -v lean4-jupyter-cache:/home/lean/.cache \
            -v lean4-jupyter-elan:/home/lean/.elan \
            -v lean4-jupyter-python:/home/lean/.venv \
            -w /workspace \
            --user 1000:1000 \
            lean4-jupyter:latest
    fi
    
    log_success "Jupyterコンテナが起動しました"
    log_info "JupyterLabにアクセスするには以下のURLを開いてください:"
    log_info "  http://localhost:8888"
    log_info ""
    log_info "コンテナの起動が完了するまで少し時間がかかる場合があります。"
}

# コンテナを停止
stop() {
    log_info "Lean4 Jupyterコンテナを停止しています..."
    cd "$SCRIPT_DIR"
    
    if command -v podman-compose &> /dev/null; then
        podman-compose down
    else
        podman stop lean4-jupyter-container || true
        podman rm lean4-jupyter-container || true
    fi
    
    log_success "コンテナを停止しました"
}

# コンテナに接続
exec() {
    log_info "Lean4 Jupyterコンテナに接続しています..."
    
    if ! podman ps | grep -q lean4-jupyter-container; then
        log_error "lean4-jupyter-containerが実行されていません"
        log_info "先に 'start' コマンドを実行してください"
        exit 1
    fi
    
    podman exec -it lean4-jupyter-container /bin/bash
}

# ログを表示
logs() {
    log_info "Lean4 Jupyterコンテナのログを表示しています..."
    
    if command -v podman-compose &> /dev/null; then
        podman-compose logs -f lean4-jupyter
    else
        podman logs -f lean4-jupyter-container
    fi
}

# ステータス確認
status() {
    log_info "Lean4 Jupyter環境の状態を確認しています..."
    
    echo "=== Podmanの状態 ==="
    podman version || log_error "Podmanが利用できません"
    
    echo -e "\n=== コンテナの状態 ==="
    if podman ps -a | grep -q lean4-jupyter-container; then
        podman ps -a | grep lean4-jupyter-container
    else
        log_warning "lean4-jupyter-containerが見つかりません"
    fi
    
    echo -e "\n=== イメージの状態 ==="
    if podman images | grep -q lean4-jupyter; then
        podman images | grep lean4-jupyter
    else
        log_warning "lean4-jupyterイメージが見つかりません"
    fi
    
    echo -e "\n=== ポートの状態 ==="
    if command -v ss &> /dev/null; then
        ss -tlnp | grep :8888 || log_info "ポート8888は使用されていません"
    elif command -v netstat &> /dev/null; then
        netstat -tlnp | grep :8888 || log_info "ポート8888は使用されていません"
    fi
}

# クリーンアップ
clean() {
    log_warning "すべてのLean4 Jupyter関連のコンテナとイメージを削除します"
    read -p "続行しますか? (y/N): " -n 1 -r
    echo
    
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        log_info "クリーンアップを実行しています..."
        
        # コンテナの停止と削除
        podman stop lean4-jupyter-container 2>/dev/null || true
        podman rm lean4-jupyter-container 2>/dev/null || true
        
        # イメージの削除
        podman rmi lean4-jupyter:latest 2>/dev/null || true
        
        # ボリュームの削除
        podman volume rm lean4-jupyter-config lean4-jupyter-notebooks \
                         lean4-jupyter-cache lean4-jupyter-elan \
                         lean4-jupyter-python 2>/dev/null || true
        
        log_success "クリーンアップが完了しました"
    else
        log_info "クリーンアップをキャンセルしました"
    fi
}

# ヘルプメッセージ
show_help() {
    echo "Lean4 Jupyter環境管理スクリプト"
    echo ""
    echo "使用方法:"
    echo "  $0 <command>"
    echo ""
    echo "コマンド:"
    echo "  build   - Lean4 Jupyter Dockerイメージをビルド"
    echo "  start   - Lean4 Jupyterコンテナを起動"
    echo "  stop    - Lean4 Jupyterコンテナを停止"
    echo "  exec    - 実行中のコンテナに接続"
    echo "  logs    - コンテナのログを表示"
    echo "  status  - 環境の状態を確認"
    echo "  clean   - すべてのコンテナとイメージを削除"
    echo "  help    - このヘルプメッセージを表示"
    echo ""
    echo "例:"
    echo "  $0 build    # イメージをビルド"
    echo "  $0 start    # コンテナを起動"
    echo "  $0 logs     # ログを確認"
    echo ""
    echo "JupyterLabへのアクセス:"
    echo "  ブラウザで http://localhost:8888 を開いてください"
}

# メイン処理
main() {
    case "${1:-help}" in
        build)
            check_podman
            build
            ;;
        start)
            check_podman
            start
            ;;
        stop)
            stop
            ;;
        exec)
            exec
            ;;
        logs)
            logs
            ;;
        status)
            status
            ;;
        clean)
            clean
            ;;
        help|--help|-h)
            show_help
            ;;
        *)
            log_error "不明なコマンド: $1"
            show_help
            exit 1
            ;;
    esac
}

main "$@"