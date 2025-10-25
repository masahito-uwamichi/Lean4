#!/bin/bash

# Lean4 Podman環境管理スクリプト

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
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
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
    log_info "Lean4 Podmanイメージをビルドしています..."
    cd "$SCRIPT_DIR"
    
    if command -v podman-compose &> /dev/null; then
        podman-compose build
    else
        podman build -t lean4-dev:latest .
    fi
    
    log_success "イメージのビルドが完了しました"
}

# コンテナを起動
start() {
    log_info "Lean4コンテナを起動しています..."
    cd "$SCRIPT_DIR"
    
    if command -v podman-compose &> /dev/null; then
        podman-compose up -d
    else
        podman run -d \
            --name lean4-container \
            -v "$PROJECT_ROOT:/workspace:Z" \
            -v lean4-cache:/home/lean/.cache \
            -v lean4-elan:/home/lean/.elan \
            -w /workspace \
            -p 8080:8080 \
            --user 1000:1000 \
            lean4-dev:latest \
            sleep infinity
    fi
    
    log_success "コンテナが起動しました"
}

# コンテナを停止
stop() {
    log_info "Lean4コンテナを停止しています..."
    cd "$SCRIPT_DIR"
    
    if command -v podman-compose &> /dev/null; then
        podman-compose down
    else
        podman stop lean4-container || true
        podman rm lean4-container || true
    fi
    
    log_success "コンテナを停止しました"
}

# コンテナに接続
exec() {
    log_info "Lean4コンテナに接続しています..."
    
    if ! podman ps | grep -q lean4-container; then
        log_error "lean4-containerが実行されていません"
        log_info "先に 'start' コマンドを実行してください"
        exit 1
    fi
    
    podman exec -it lean4-container /bin/bash
}

# ステータス確認
status() {
    log_info "Lean4環境の状態を確認しています..."
    
    echo "=== Podmanの状態 ==="
    podman version || log_error "Podmanが利用できません"
    
    echo -e "\n=== コンテナの状態 ==="
    if podman ps -a | grep -q lean4-container; then
        podman ps -a | grep lean4-container
    else
        log_warning "lean4-containerが見つかりません"
    fi
    
    echo -e "\n=== イメージの状態 ==="
    if podman images | grep -q lean4-dev; then
        podman images | grep lean4-dev
    else
        log_warning "lean4-devイメージが見つかりません"
    fi
}

# クリーンアップ
clean() {
    log_warning "すべてのLean4関連のコンテナとイメージを削除します"
    read -p "続行しますか? (y/N): " -n 1 -r
    echo
    
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        log_info "クリーンアップを実行しています..."
        
        # コンテナの停止と削除
        podman stop lean4-container 2>/dev/null || true
        podman rm lean4-container 2>/dev/null || true
        
        # イメージの削除
        podman rmi lean4-dev:latest 2>/dev/null || true
        
        # ボリュームの削除
        podman volume rm lean4-cache lean4-elan 2>/dev/null || true
        
        log_success "クリーンアップが完了しました"
    else
        log_info "クリーンアップをキャンセルしました"
    fi
}

# ヘルプメッセージ
show_help() {
    echo "Lean4 Podman環境管理スクリプト"
    echo ""
    echo "使用方法:"
    echo "  $0 <command>"
    echo ""
    echo "コマンド:"
    echo "  build   - Lean4 Dockerイメージをビルド"
    echo "  start   - Lean4コンテナを起動"
    echo "  stop    - Lean4コンテナを停止"
    echo "  exec    - 実行中のコンテナに接続"
    echo "  status  - 環境の状態を確認"
    echo "  clean   - すべてのコンテナとイメージを削除"
    echo "  help    - このヘルプメッセージを表示"
    echo ""
    echo "例:"
    echo "  $0 build    # イメージをビルド"
    echo "  $0 start    # コンテナを起動"
    echo "  $0 exec     # コンテナに接続"
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