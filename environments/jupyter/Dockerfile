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

# Mathlibプロジェクトのセットアップ (完全版 - Batteriesを含む)
WORKDIR /home/$USERNAME
RUN mkdir -p mathlib-project && cd mathlib-project && \
    lake init mathlib-project

# 正しいlakefile.leanを作成（Batteriesも含む）
RUN cd mathlib-project && \
    cat > lakefile.lean << 'EOF'
import Lake
open Lake DSL

package «mathlib-project» where
  -- add package configuration options here

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.11.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

@[default_target]
lean_lib «MathLibProject» where
  -- add library configuration options here
EOF

# Mathlibとその依存関係をビルド
RUN cd mathlib-project && \
    echo "Updating dependencies..." && \
    timeout 1800 lake update && \
    echo "Building Mathlib and Batteries (this may take 60+ minutes)..." && \
    timeout 10800 lake build || echo "Build may have failed or timed out - checking partial build"

# ビルド状況の詳細チェック
RUN cd mathlib-project && \
    echo "=== Lake manifest ===" && \
    cat lake-manifest.json && \
    echo "=== Package structure ===" && \
    ls -la .lake/packages/ && \
    echo "=== Batteries check ===" && \
    ls -la .lake/packages/batteries/ || echo "Batteries not found" && \
    echo "=== Mathlib check ===" && \
    ls -la .lake/packages/mathlib/ || echo "Mathlib not found" && \
    echo "=== .olean files sample ===" && \
    find .lake -name "*.olean" | head -20 || echo "No .olean files found"

# LEAN_PATH環境変数の設定 (Batteriesも含む)
ENV LEAN_PATH="/home/$USERNAME/mathlib-project/.lake/packages/batteries/.lake/build/lib:/home/$USERNAME/mathlib-project/.lake/packages/mathlib/.lake/build/lib:/home/$USERNAME/mathlib-project/.lake/build/lib:$LEAN_PATH"

# 作業ディレクトリの設定
WORKDIR /workspace

# Jupyterのポートを公開
EXPOSE 8888

# JupyterLabをデフォルトで起動
CMD ["jupyter", "lab", "--ip=0.0.0.0", "--port=8888", "--no-browser", "--allow-root", "--NotebookApp.token=''", "--NotebookApp.password=''"]