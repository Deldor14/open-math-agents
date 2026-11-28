"""Run the PARI certificate with strict error handling."""
from pathlib import Path
import shutil
import subprocess
import sys

if __name__ == '__main__':
    gp = str(Path(sys.argv[1]).resolve()) if len(sys.argv)>1 else shutil.which('gp')
    if not gp:
        raise SystemExit('PARI/GP executable required')
    result = subprocess.run(
        [gp,'-qf','-s','256M'],cwd=Path(__file__).resolve().parent,
        input='iferr(read("verify_local.gp"),E,print(E);quit(1));quit(0)\n',
        text=True,capture_output=True,
    )
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    if result.returncode or '***' in result.stderr or 'dimension 1.' not in result.stdout:
        raise SystemExit(1)
