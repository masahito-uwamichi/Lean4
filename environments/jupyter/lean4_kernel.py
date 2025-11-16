#!/usr/bin/env python3
"""
Lean4 Jupyter カーネル
Lean4コードを実行し、Jupyter Notebookとの統合を提供します。
"""

import sys
import os
import subprocess
import tempfile
import json
import uuid
from pathlib import Path

from ipykernel.kernelbase import Kernel

class Lean4Kernel(Kernel):
    implementation = 'Lean4'
    implementation_version = '1.0'
    language = 'lean4'
    language_version = '4.11.0'
    language_info = {
        'name': 'lean4',
        'mimetype': 'text/x-lean',
        'file_extension': '.lean',
        'pygments_lexer': 'lean',
        'codemirror_mode': 'lean',
        'help_links': [
            {
                'text': 'Lean4 Documentation',
                'url': 'https://lean-lang.org/lean4/doc/',
            },
        ],
    }
    banner = "Lean4 Kernel - A kernel for running Lean4 code in Jupyter with Mathlib support"

    def __init__(self, **kwargs):
        Kernel.__init__(self, **kwargs)
        self.lean_executable = self._find_lean_executable()
        self.mathlib_project_path = self._find_mathlib_project()

    def _find_lean_executable(self):
        """Lean実行ファイルを探す"""
        lean_paths = [
            '/home/lean/.elan/bin/lean',
            '/usr/local/bin/lean',
            '/usr/bin/lean'
        ]
        
        for path in lean_paths:
            if os.path.exists(path):
                return path
        
        # PATHから検索
        try:
            result = subprocess.run(['which', 'lean'], 
                                  capture_output=True, text=True, check=True)
            return result.stdout.strip()
        except subprocess.CalledProcessError:
            return 'lean'  # フォールバック

    def _find_mathlib_project(self):
        """Mathlibプロジェクトのパスを探す"""
        mathlib_paths = [
            '/home/lean/mathlib-project',
            '/workspace/mathlib-project',
            '/home/lean/.local/mathlib-project',
            os.path.expanduser('~/mathlib-project')
        ]
        
        for path in mathlib_paths:
            lakefile_path = os.path.join(path, 'lakefile.lean')
            manifest_path = os.path.join(path, 'lake-manifest.json')
            
            if os.path.exists(lakefile_path):
                # lake-manifest.jsonの存在も確認（依存関係がセットアップ済み）
                if os.path.exists(manifest_path):
                    print(f"Found Mathlib project at: {path}")
                    return path
                else:
                    print(f"Found lakefile.lean but no lake-manifest.json at: {path}")
        
        print("No Mathlib project found")
        return None

    def do_execute(self, code, silent, store_history=True, user_expressions=None, allow_stdin=False):
        """
        Lean4コードを実行する
        """
        if not code.strip():
            return {'status': 'ok', 'execution_count': self.execution_count, 
                   'payload': [], 'user_expressions': {}}

        try:
            # Mathlibプロジェクト内で実行するかを決定
            use_mathlib = self._needs_mathlib(code)
            
            if use_mathlib and self.mathlib_project_path:
                result = self._run_with_mathlib(code)
            else:
                result = self._run_standalone(code)
            
            if result['status'] == 'ok':
                self._send_output(result['output'], 'stdout')
            else:
                self._send_output(result['error'], 'stderr')

            return {'status': result['status'], 'execution_count': self.execution_count,
                   'payload': [], 'user_expressions': {}}

        except Exception as e:
            self._send_output(f'Error: {str(e)}', 'stderr')
            return {'status': 'error', 'execution_count': self.execution_count,
                   'payload': [], 'user_expressions': {}}

    def _needs_mathlib(self, code):
        """コードがMathlibを必要とするかを判定"""
        mathlib_indicators = [
            'import Mathlib',
            'import Batteries',
            'import Aesop', 
            'import Std',
            'ℝ', 'Real', 
            'Group', 'Ring', 'Field',
            'Real.pi', 'Real.exp',
            'add_comm', 'mul_assoc',
            '∧', '∨', '¬',  # これらもMathlibで定義されている
            'norm_num', 'linarith', 'ring',  # Mathlibのタクティク
            'simp_all', 'omega'  # Mathlibの高度なタクティク
        ]
        
        # 基本的なLean4のコア機能のみを使うケース
        basic_only_indicators = [
            '#eval', '#check', '#print',
            'def main', 'theorem', 'example'
        ]
        
        # Mathlibが必要かを判定
        needs_mathlib = any(indicator in code for indicator in mathlib_indicators)
        
        # デバッグ用の出力
        if needs_mathlib:
            print(f"Code needs Mathlib: {code[:50]}...")
        else:
            print(f"Code uses basic Lean4: {code[:50]}...")
            
        return needs_mathlib

    def _run_with_mathlib(self, code):
        """Mathlibプロジェクト内でLeanコードを実行"""
        try:
            # Mathlibプロジェクト内に一時ファイルを作成
            temp_dir = os.path.join(self.mathlib_project_path, 'temp')
            os.makedirs(temp_dir, exist_ok=True)
            
            temp_file = os.path.join(temp_dir, f'temp_{uuid.uuid4().hex[:8]}.lean')
            
            with open(temp_file, 'w') as f:
                f.write(code)

            # Lakeを使ってMathlibプロジェクト内で実行（より確実）
            try:
                # まずlake使用を試行
                result = subprocess.run(
                    ['lake', 'env', 'lean', temp_file],
                    cwd=self.mathlib_project_path,
                    capture_output=True,
                    text=True,
                    timeout=90
                )
            except FileNotFoundError:
                # lakeが見つからない場合は直接leanを使用
                result = subprocess.run(
                    [self.lean_executable, temp_file],
                    cwd=self.mathlib_project_path,
                    capture_output=True,
                    text=True,
                    timeout=90
                )
            
            # 一時ファイルを削除
            os.unlink(temp_file)
            
            if result.returncode == 0:
                output = result.stdout if result.stdout else "✓ Code compiled successfully with Mathlib"
                return {'status': 'ok', 'output': output}
            else:
                error_msg = result.stderr if result.stderr else result.stdout
                # 追加のデバッグ情報
                debug_info = f"\n[Debug] Working directory: {self.mathlib_project_path}"
                debug_info += f"\n[Debug] LEAN_PATH: {os.environ.get('LEAN_PATH', 'Not set')}"
                return {'status': 'error', 'error': error_msg + debug_info}
                
        except subprocess.TimeoutExpired:
            return {'status': 'error', 'error': 'Execution timed out (90s limit)'}
        except Exception as e:
            return {'status': 'error', 'error': f'Mathlib execution error: {str(e)}'}

    def _run_standalone(self, code):
        """スタンドアロンでLeanコードを実行"""
        try:
            # 一時的なLean4ファイルを作成
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                # 基本的なimportを追加（Mathlibなし）
                lean_code = self._prepare_basic_lean_code(code)
                f.write(lean_code)
                temp_file = f.name

            # Lean4でコードをチェック
            result = subprocess.run(
                [self.lean_executable, temp_file],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # 一時ファイルを削除
            os.unlink(temp_file)

            if result.returncode == 0:
                output = result.stdout if result.stdout else "✓ Code compiled successfully"
                return {'status': 'ok', 'output': output}
            else:
                error_msg = result.stderr if result.stderr else result.stdout
                return {'status': 'error', 'error': error_msg}
                
        except subprocess.TimeoutExpired:
            return {'status': 'error', 'error': 'Execution timed out (30s limit)'}
        except FileNotFoundError:
            return {'status': 'error', 'error': f'Lean executable not found: {self.lean_executable}'}
        except Exception as e:
            return {'status': 'error', 'error': f'Execution error: {str(e)}'}

    def _prepare_basic_lean_code(self, code):
        """
        基本的なLean4コード（Mathlibなし）を準備する
        """
        # コードが既にimportを含んでいる場合はそのまま使用
        if 'import ' in code or 'namespace ' in code:
            return code
        
        # #eval や #check コマンドや単純な定義の場合は、importなしで実行を試行
        if code.strip().startswith('#') or 'def ' in code or 'theorem ' in code:
            return code
        
        # その他の場合は基本的なimportを追加
        basic_imports = [
            "import Init.Data.Nat.Basic",
            "import Init.Logic",
            ""
        ]
        
        return '\n'.join(basic_imports) + '\n' + code



    def _send_output(self, text, stream_name):
        """
        出力をJupyterに送信する
        """
        if not text.strip():
            return
            
        stream_content = {'name': stream_name, 'text': text}
        self.send_response(self.iopub_socket, 'stream', stream_content)

    def do_complete(self, code, cursor_pos):
        """
        コード補完機能（基本的な実装）
        """
        # 基本的なLean4キーワードとタクティク
        lean_keywords = [
            'theorem', 'def', 'lemma', 'example', 'structure', 'inductive',
            'namespace', 'import', 'export', 'open', 'variable', 'universe',
            'by', 'have', 'show', 'from', 'where', 'let', 'in',
            'rw', 'simp', 'exact', 'apply', 'cases', 'induction', 'constructor',
            'left', 'right', 'split', 'contradiction', 'sorry', 'trivial',
            'linarith', 'ring', 'norm_num', 'decide'
        ]
        
        # カーソル位置から単語の開始位置を見つける
        start_pos = cursor_pos
        while start_pos > 0 and (code[start_pos - 1].isalnum() or code[start_pos - 1] == '_'):
            start_pos -= 1
        
        partial_word = code[start_pos:cursor_pos]
        
        # マッチする補完候補を探す
        matches = [kw for kw in lean_keywords if kw.startswith(partial_word)]
        
        return {
            'matches': matches,
            'cursor_start': start_pos,
            'cursor_end': cursor_pos,
            'metadata': {},
            'status': 'ok'
        }

if __name__ == '__main__':
    from ipykernel.kernelapp import IPKernelApp
    IPKernelApp.launch_instance(kernel_class=Lean4Kernel)