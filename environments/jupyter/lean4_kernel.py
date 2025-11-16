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
    language_version = '4.12.0'
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
    banner = "Lean4 Kernel - A kernel for running Lean4 code in Jupyter"

    def __init__(self, **kwargs):
        Kernel.__init__(self, **kwargs)
        self.lean_executable = self._find_lean_executable()

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

    def do_execute(self, code, silent, store_history=True, user_expressions=None, allow_stdin=False):
        """
        Lean4コードを実行する
        """
        if not code.strip():
            return {'status': 'ok', 'execution_count': self.execution_count, 
                   'payload': [], 'user_expressions': {}}

        try:
            # 一時的なLean4ファイルを作成
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                # 基本的なimportを追加
                lean_code = self._prepare_lean_code(code)
                f.write(lean_code)
                temp_file = f.name

            # Lean4でコードをチェック
            result = self._run_lean(temp_file)
            
            # 一時ファイルを削除
            os.unlink(temp_file)

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

    def _prepare_lean_code(self, code):
        """
        Lean4コードを実行可能な形式に準備する
        """
        # コードが既にimportを含んでいる場合はそのまま使用
        if 'import ' in code or 'namespace ' in code:
            return code
        
        # 基本的なimportを追加
        basic_imports = [
            "import Mathlib.Data.Nat.Basic",
            "import Mathlib.Data.Real.Basic",
            "import Mathlib.Tactic",
            ""
        ]
        
        # #eval や #check コマンドの場合は、そのまま実行
        if code.strip().startswith('#'):
            return '\n'.join(basic_imports) + code
        
        # 定理や定義の場合
        return '\n'.join(basic_imports) + '\n' + code

    def _run_lean(self, file_path):
        """
        Leanファイルを実行し、結果を取得する
        """
        try:
            # まずLeanでファイルをチェック
            result = subprocess.run(
                [self.lean_executable, file_path],
                capture_output=True,
                text=True,
                timeout=30
            )
            
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