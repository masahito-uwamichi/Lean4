@echo off
setlocal enabledelayedexpansion

REM Lean4 Podman環境管理スクリプト (Windows PowerShell版)

set "SCRIPT_DIR=%~dp0"
set "PROJECT_ROOT=%SCRIPT_DIR%..\.."

REM カラー出力の設定 (PowerShellで使用)
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
echo %BLUE%[INFO]%NC% Lean4 Podmanイメージをビルドしています...
cd /d "%SCRIPT_DIR%"

where podman-compose >nul 2>&1
if errorlevel 1 (
    podman build -t lean4-dev:latest .
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
echo %BLUE%[INFO]%NC% Lean4コンテナを起動しています...
cd /d "%SCRIPT_DIR%"

where podman-compose >nul 2>&1
if errorlevel 1 (
    podman run -d --name lean4-container -v "%PROJECT_ROOT%:/workspace:Z" -v lean4-cache:/home/lean/.cache -v lean4-elan:/home/lean/.elan -w /workspace -p 8080:8080 --user 1000:1000 lean4-dev:latest sleep infinity
) else (
    podman-compose up -d
)

if errorlevel 1 (
    echo %RED%[ERROR]%NC% コンテナの起動に失敗しました
    exit /b 1
)

echo %GREEN%[SUCCESS]%NC% コンテナが起動しました
goto :eof

:stop
echo %BLUE%[INFO]%NC% Lean4コンテナを停止しています...
cd /d "%SCRIPT_DIR%"

where podman-compose >nul 2>&1
if errorlevel 1 (
    podman stop lean4-container 2>nul
    podman rm lean4-container 2>nul
) else (
    podman-compose down
)

echo %GREEN%[SUCCESS]%NC% コンテナを停止しました
goto :eof

:exec
echo %BLUE%[INFO]%NC% Lean4コンテナに接続しています...

podman ps | findstr lean4-container >nul
if errorlevel 1 (
    echo %RED%[ERROR]%NC% lean4-containerが実行されていません
    echo %BLUE%[INFO]%NC% 先に 'start' コマンドを実行してください
    exit /b 1
)

podman exec -it lean4-container /bin/bash
goto :eof

:status
echo %BLUE%[INFO]%NC% Lean4環境の状態を確認しています...

echo === Podmanの状態 ===
podman version
if errorlevel 1 (
    echo %RED%[ERROR]%NC% Podmanが利用できません
)

echo.
echo === コンテナの状態 ===
podman ps -a | findstr lean4-container
if errorlevel 1 (
    echo %YELLOW%[WARNING]%NC% lean4-containerが見つかりません
)

echo.
echo === イメージの状態 ===
podman images | findstr lean4-dev
if errorlevel 1 (
    echo %YELLOW%[WARNING]%NC% lean4-devイメージが見つかりません
)
goto :eof

:clean
echo %YELLOW%[WARNING]%NC% すべてのLean4関連のコンテナとイメージを削除します
set /p "REPLY=続行しますか? (y/N): "

if /i "%REPLY%"=="y" (
    echo %BLUE%[INFO]%NC% クリーンアップを実行しています...
    
    podman stop lean4-container 2>nul
    podman rm lean4-container 2>nul
    podman rmi lean4-dev:latest 2>nul
    podman volume rm lean4-cache lean4-elan 2>nul
    
    echo %GREEN%[SUCCESS]%NC% クリーンアップが完了しました
) else (
    echo %BLUE%[INFO]%NC% クリーンアップをキャンセルしました
)
goto :eof

:help
echo Lean4 Podman環境管理スクリプト
echo.
echo 使用方法:
echo   %~nx0 ^<command^>
echo.
echo コマンド:
echo   build   - Lean4 Dockerイメージをビルド
echo   start   - Lean4コンテナを起動
echo   stop    - Lean4コンテナを停止
echo   exec    - 実行中のコンテナに接続
echo   status  - 環境の状態を確認
echo   clean   - すべてのコンテナとイメージを削除
echo   help    - このヘルプメッセージを表示
echo.
echo 例:
echo   %~nx0 build    # イメージをビルド
echo   %~nx0 start    # コンテナを起動
echo   %~nx0 exec     # コンテナに接続
goto :eof