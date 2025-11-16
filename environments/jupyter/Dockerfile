# Lean4 Jupyter開発環境用のDockerfile
FROM ubuntu:22.04

# 環境変数の設定
ENV DEBIAN_FRONTEND=noninteractive
ENV LEAN_VERSION=v4.11.0

# 必要なパッケージのインストール
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    cmake \
    python3 \
    python3-pip \
    python3-venv \
    pkg-config \
    libgmp-dev \
    libssl-dev \
    wget \
    unzip \
    nodejs \
    npm \
    ca-certificates \
    sudo \
    && rm -rf /var/lib/apt/lists/*

# Update CA certificates for better HTTPS support
RUN update-ca-certificates

# ユーザーの作成
ARG USERNAME=lean
ARG USER_UID=1000
ARG USER_GID=$USER_UID

RUN groupadd --gid $USER_GID $USERNAME \
    && useradd --uid $USER_UID --gid $USER_GID -m $USERNAME \
    && echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME \
    && chmod 0440 /etc/sudoers.d/$USERNAME

# ユーザーを切り替え
USER $USERNAME
WORKDIR /home/$USERNAME

# Python仮想環境の作成 (先にやる)
RUN python3 -m venv /home/$USERNAME/.venv
ENV PATH="/home/$USERNAME/.venv/bin:$PATH"

# Jupyter関連パッケージのインストール (先にやる)
RUN pip install --upgrade pip && \
    pip install jupyterlab \
                jupyter \
                notebook \
                ipywidgets \
                ipykernel \
                pygments \
                requests

# elanのインストール (Lean toolchain manager) - 改良版
RUN curl --connect-timeout 30 --max-time 300 --retry 5 --retry-delay 10 \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf -o elan-init.sh && \
    chmod +x elan-init.sh && \
    ./elan-init.sh -y --default-toolchain $LEAN_VERSION && \
    rm elan-init.sh
ENV PATH="/home/$USERNAME/.elan/bin:$PATH"

# Lean4が正常にインストールされたか確認
RUN which lean && lean --version

# Lake (Lean package manager) の確認
RUN which lake && lake --version

# カスタムLean4カーネルの設定ディレクトリを作成
RUN mkdir -p /home/$USERNAME/.local/share/jupyter/kernels/lean4

# Lean4カーネル設定ファイルを作成
COPY --chown=$USERNAME:$USERNAME kernel.json /home/$USERNAME/.local/share/jupyter/kernels/lean4/
COPY --chown=$USERNAME:$USERNAME lean4_kernel.py /home/$USERNAME/.local/share/jupyter/kernels/lean4/

# Lean4カーネルスクリプトを実行可能にする
RUN chmod +x /home/$USERNAME/.local/share/jupyter/kernels/lean4/lean4_kernel.py

# JupyterLabの拡張機能をインストール
RUN jupyter labextension install @jupyter-widgets/jupyterlab-manager --no-build || echo "Extension installation failed, continuing..."

# Mathlib環境のセットアップ（手動作成方式）
WORKDIR /home/$USERNAME

# 新しいプロジェクトを作成してMathlibを手動で設定
RUN echo "Creating Mathlib project manually..." && \
    lake new mathlib-project && \
    cd mathlib-project

# lakefile.leanを最もシンプルな形で作成
RUN cd mathlib-project && \
    echo "Setting up minimal lakefile.lean..." && \
    cat > lakefile.lean << 'EOF'
import Lake
open Lake DSL

package «mathlib-project» where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MathLibProject» where
EOF

# 段階的なセットアップ
RUN cd mathlib-project && \
    echo "Step 1: Update dependencies..." && \
    timeout 1200 lake update || echo "Update completed or failed" && \
    echo "Step 2: Try to get prebuilt cache..." && \
    timeout 600 lake exe cache get || echo "Cache not available" && \
    echo "Step 3: Basic build attempt..." && \
    timeout 1800 lake build || echo "Build attempted"

# ビルド状況の詳細確認
RUN cd mathlib-project && \
    echo "=== Project structure ===" && \
    ls -la && \
    echo "=== Dependencies downloaded ===" && \
    ls -la .lake/packages/ && \
    echo "=== Mathlib package check ===" && \
    if [ -d ".lake/packages/mathlib" ]; then \
        echo "Mathlib package found"; \
        ls -la .lake/packages/mathlib/.lake/build/lib/Mathlib/ | head -5 || echo "Lib directory not ready"; \
    else \
        echo "Mathlib package not found"; \
    fi && \
    echo "=== .olean files status ===" && \
    OLEAN_COUNT=$(find .lake -name "*.olean" | wc -l) && \
    echo "Found $OLEAN_COUNT .olean files" && \
    find .lake -name "*.olean" | head -10

# LEAN_PATH環境変数の動的설정
RUN cd mathlib-project && \
    echo "=== Setting up LEAN_PATH ===" && \
    PROJECT_LIB="$PWD/.lake/build/lib" && \
    MATHLIB_LIB="" && \
    if [ -d ".lake/packages/mathlib/.lake/build/lib" ]; then \
        MATHLIB_LIB=":$PWD/.lake/packages/mathlib/.lake/build/lib"; \
    fi && \
    EXTRA_LIBS=$(find .lake/packages -name lib -type d 2>/dev/null | grep -v mathlib | tr '\n' ':' | sed 's/:$//') && \
    FULL_PATH="$PROJECT_LIB$MATHLIB_LIB" && \
    if [ -n "$EXTRA_LIBS" ]; then \
        FULL_PATH="$FULL_PATH:$EXTRA_LIBS"; \
    fi && \
    echo "Final LEAN_PATH: $FULL_PATH"

# 基本的なLEAN_PATH設定（フォールバック）
ENV LEAN_PATH="/home/$USERNAME/mathlib-project/.lake/build/lib:/home/$USERNAME/mathlib-project/.lake/packages/mathlib/.lake/build/lib"

# 最終的な環境チェック
RUN cd mathlib-project && \
    echo "=== Final environment check ===" && \
    echo "Lean version: $(lean --version)" && \
    echo "Lake version: $(lake --version)" && \
    echo "Project directory: $PWD" && \
    echo "LEAN_PATH: $LEAN_PATH" && \
    ls -la lakefile.lean && \
    echo "=== Ready for Jupyter ===" || echo "Setup completed with warnings"

# 作業ディレクトリの設定
WORKDIR /workspace

# Jupyterのポートを公開
EXPOSE 8888

# JupyterLabをデフォルトで起動
CMD ["jupyter", "lab", "--ip=0.0.0.0", "--port=8888", "--no-browser", "--allow-root", "--NotebookApp.token=''", "--NotebookApp.password=''"]