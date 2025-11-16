@echo off
setlocal enabledelayedexpansion

REM Lean4 Jupyter環境管理スクリプト (Windows版)

set "SCRIPT_DIR=%~dp0"
set "PROJECT_ROOT=%SCRIPT_DIR%..\.."

REM カラー出力の設定
set "RED=[91m"
set "GREEN=[92m"
set "YELLOW=[93m"
set "BLUE=[94m"
set "NC=[0m"

if "%1"=="" goto :help
if "%1"=="help" goto :help
if "%1"=="--help" goto :help
if "%1"=="-h" goto :help
if "%1"=="build" goto :build
if "%1"=="start" goto :start
if "%1"=="stop" goto :stop
if "%1"=="exec" goto :exec
if "%1"=="logs" goto :logs
if "%1"=="status" goto :status
if "%1"=="clean" goto :clean

echo %RED%[ERROR]%NC% 不明なコマンド: %1
goto :help

:check_podman
where podman >nul 2>&1
if errorlevel 1 (
    echo %RED%[ERROR]%NC% Podmanがインストールされていません
    echo %BLUE%[INFO]%NC% 以下の方法でインストールしてください:
    echo %BLUE%[INFO]%NC%   Windows: https://podman.io/getting-started/installation
    exit /b 1
)

where podman-compose >nul 2>&1
if errorlevel 1 (
    echo %YELLOW%[WARNING]%NC% podman-composeがインストールされていません
    echo %BLUE%[INFO]%NC% 以下のコマンドでインストールしてください:
    echo %BLUE%[INFO]%NC%   pip3 install podman-compose
)
goto :eof

:build
call :check_podman
echo %BLUE%[INFO]%NC% Lean4 Jupyter環境をビルドしています...
cd /d "%SCRIPT_DIR%"

where podman-compose >nul 2>&1
if errorlevel 1 (
    podman build -t lean4-jupyter:latest .
) else (
    podman-compose build
)

if errorlevel 1 (
    echo %RED%[ERROR]%NC% ビルドに失敗しました
    exit /b 1
)

echo %GREEN%[SUCCESS]%NC% イメージのビルドが完了しました
goto :eof

:start
call :check_podman
echo %BLUE%[INFO]%NC% Lean4 Jupyterコンテナを起動しています...
cd /d "%SCRIPT_DIR%"

where podman-compose >nul 2>&1
if errorlevel 1 (
    podman run -d --name lean4-jupyter-container -p 8888:8888 -v "%PROJECT_ROOT%:/workspace:Z" -v lean4-jupyter-config:/home/lean/.jupyter -v lean4-jupyter-notebooks:/home/lean/notebooks -v lean4-jupyter-cache:/home/lean/.cache -v lean4-jupyter-elan:/home/lean/.elan -v lean4-jupyter-python:/home/lean/.venv -w /workspace --user 1000:1000 lean4-jupyter:latest
) else (
    podman-compose up -d
)

if errorlevel 1 (
    echo %RED%[ERROR]%NC% コンテナの起動に失敗しました
    exit /b 1
)

echo %GREEN%[SUCCESS]%NC% Jupyterコンテナが起動しました
echo %BLUE%[INFO]%NC% JupyterLabにアクセスするには以下のURLを開いてください:
echo %BLUE%[INFO]%NC%   http://localhost:8888
echo %BLUE%[INFO]%NC%
echo %BLUE%[INFO]%NC% コンテナの起動が完了するまで少し時間がかかる場合があります。
goto :eof

:stop
echo %BLUE%[INFO]%NC% Lean4 Jupyterコンテナを停止しています...
cd /d "%SCRIPT_DIR%"

where podman-compose >nul 2>&1
if errorlevel 1 (
    podman stop lean4-jupyter-container 2>nul
    podman rm lean4-jupyter-container 2>nul
) else (
    podman-compose down
)

echo %GREEN%[SUCCESS]%NC% コンテナを停止しました
goto :eof

:exec
echo %BLUE%[INFO]%NC% Lean4 Jupyterコンテナに接続しています...

podman ps | findstr lean4-jupyter-container >nul
if errorlevel 1 (
    echo %RED%[ERROR]%NC% lean4-jupyter-containerが実行されていません
    echo %BLUE%[INFO]%NC% 先に 'start' コマンドを実行してください
    exit /b 1
)

podman exec -it lean4-jupyter-container /bin/bash
goto :eof

:logs
echo %BLUE%[INFO]%NC% Lean4 Jupyterコンテナのログを表示しています...

where podman-compose >nul 2>&1
if errorlevel 1 (
    podman logs -f lean4-jupyter-container
) else (
    podman-compose logs -f lean4-jupyter
)
goto :eof

:status
echo %BLUE%[INFO]%NC% Lean4 Jupyter環境の状態を確認しています...

echo === Podmanの状態 ===
podman version
if errorlevel 1 (
    echo %RED%[ERROR]%NC% Podmanが利用できません
)

echo.
echo === コンテナの状態 ===
podman ps -a | findstr lean4-jupyter-container
if errorlevel 1 (
    echo %YELLOW%[WARNING]%NC% lean4-jupyter-containerが見つかりません
)

echo.
echo === イメージの状態 ===
podman images | findstr lean4-jupyter
if errorlevel 1 (
    echo %YELLOW%[WARNING]%NC% lean4-jupyterイメージが見つかりません
)

echo.
echo === ポートの状態 ===
netstat -an | findstr :8888
if errorlevel 1 (
    echo %BLUE%[INFO]%NC% ポート8888は使用されていません
)
goto :eof

:clean
echo %YELLOW%[WARNING]%NC% すべてのLean4 Jupyter関連のコンテナとイメージを削除します
set /p "REPLY=続行しますか? (y/N): "

if /i "%REPLY%"=="y" (
    echo %BLUE%[INFO]%NC% クリーンアップを実行しています...
    
    podman stop lean4-jupyter-container 2>nul
    podman rm lean4-jupyter-container 2>nul
    podman rmi lean4-jupyter:latest 2>nul
    podman volume rm lean4-jupyter-config lean4-jupyter-notebooks lean4-jupyter-cache lean4-jupyter-elan lean4-jupyter-python 2>nul
    
    echo %GREEN%[SUCCESS]%NC% クリーンアップが完了しました
) else (
    echo %BLUE%[INFO]%NC% クリーンアップをキャンセルしました
)
goto :eof

:help
echo Lean4 Jupyter環境管理スクリプト
echo.
echo 使用方法:
echo   %~nx0 ^<command^>
echo.
echo コマンド:
echo   build   - Lean4 Jupyter Dockerイメージをビルド
echo   start   - Lean4 Jupyterコンテナを起動
echo   stop    - Lean4 Jupyterコンテナを停止
echo   exec    - 実行中のコンテナに接続
echo   logs    - コンテナのログを表示
echo   status  - 環境の状態を確認
echo   clean   - すべてのコンテナとイメージを削除
echo   help    - このヘルプメッセージを表示
echo.
echo 例:
echo   %~nx0 build    # イメージをビルド
echo   %~nx0 start    # コンテナを起動
echo   %~nx0 logs     # ログを確認
echo.
echo JupyterLabへのアクセス:
echo   ブラウザで http://localhost:8888 を開いてください
goto :eof