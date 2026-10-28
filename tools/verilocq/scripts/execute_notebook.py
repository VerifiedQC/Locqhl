"""Execute Quickstart using this interpreter, with all runtime files local."""

import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
runtime = ROOT / ".runtime"
for variable, directory in {
    "IPYTHONDIR": runtime / "ipython",
    "JUPYTER_RUNTIME_DIR": runtime / "jupyter",
    "JUPYTER_CONFIG_DIR": runtime / "config",
    "MPLCONFIGDIR": runtime / "matplotlib",
}.items():
    directory.mkdir(parents=True, exist_ok=True)
    os.environ[variable] = str(directory)

# An ephemeral kernelspec avoids changing the user's installed Jupyter kernels.
data = runtime / "share" / "jupyter"
kernel = data / "kernels" / "python3"
kernel.mkdir(parents=True, exist_ok=True)
(kernel / "kernel.json").write_text(json.dumps({
    "argv": [sys.executable, "-m", "ipykernel_launcher", "-f", "{connection_file}"],
    "display_name": "Python (VeriLocQ .venv)", "language": "python",
}), encoding="utf-8")
os.environ["JUPYTER_PATH"] = str(data)

import nbformat
from nbclient import NotebookClient

path = ROOT / "Quickstart.ipynb"
notebook = nbformat.read(path, as_version=4)
client = NotebookClient(notebook, timeout=120, kernel_name="python3",
                        resources={"metadata": {"path": str(ROOT)}})
client.execute()
nbformat.validate(notebook)
executed_path=path.with_name(".Quickstart.executed.ipynb")
nbformat.write(notebook, executed_path)
executed_path.replace(path)
cells = [c for c in notebook.cells if c.cell_type == "code"]
print(f"Executed {len(cells)} code cells; notebook saved with outputs: {path}")
