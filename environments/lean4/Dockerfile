# Lean4開発環境用のDockerfile
FROM ubuntu:22.04

# 環境変数の設定
ENV DEBIAN_FRONTEND=noninteractive
ENV LEAN_VERSION=v4.12.0

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
    texlive-full \
    texlive-lang-japanese \
    texlive-fonts-recommended \
    texlive-fonts-extra \
    latexmk \
    pandoc \
    nodejs \
    npm \
    && rm -rf /var/lib/apt/lists/*

# ユーザーの作成
ARG USERNAME=lean
ARG USER_UID=1000
ARG USER_GID=$USER_UID

RUN groupadd --gid $USER_GID $USERNAME \
    && useradd --uid $USER_UID --gid $USER_GID -m $USERNAME \
    && apt-get update \
    && apt-get install -y sudo \
    && echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME \
    && chmod 0440 /etc/sudoers.d/$USERNAME

# elanのインストール (Lean toolchain manager)
USER $USERNAME
WORKDIR /home/$USERNAME

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain $LEAN_VERSION
ENV PATH="/home/$USERNAME/.elan/bin:$PATH"

# Lean4の確認
RUN lean --version

# Lake (Lean package manager) の確認
RUN lake --version

# Python仮想環境の作成と必要なパッケージのインストール
RUN python3 -m venv /home/$USERNAME/.venv
ENV PATH="/home/$USERNAME/.venv/bin:$PATH"

# Python パッケージのインストール
RUN pip install --upgrade pip && \
    pip install pygments

# 作業ディレクトリの設定
WORKDIR /workspace

# ポートの公開 (Lean Language Serverなどで使用)
EXPOSE 8080

# デフォルトコマンド
CMD ["/bin/bash"]