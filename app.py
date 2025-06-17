import os
import sys
import zipfile
import subprocess
from flask import Flask, request, render_template_string

app = Flask(__name__)

# ─── Directories ──────────────────────────────────────────────────────────────
BASE_DIR    = os.path.dirname(os.path.abspath(__file__))
MODULE_DIR  = os.path.join(BASE_DIR, 'c2p')
SAMPLES_DIR = os.path.join(BASE_DIR, 'samples')
ZIP_PATH    = os.path.join(BASE_DIR, 'PPP1.zip')
PML_OUT     = os.path.join(BASE_DIR, 'main.pml')

os.makedirs(SAMPLES_DIR, exist_ok=True)

if os.path.isfile(ZIP_PATH) and not os.path.isdir(MODULE_DIR):
    with zipfile.ZipFile(ZIP_PATH, 'r') as z:
        z.extractall(BASE_DIR)

# ─── HTML Template ────────────────────────────────────────────────────────────
HTML = '''
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <title>C → Promela Converter</title>
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <style>
    *, *::before, *::after { box-sizing: border-box; }
    body {
      margin: 0;
      font-family: 'Segoe UI', sans-serif;
      background: #111;
      color: #EEE;
    }
    .container {
      max-width: 1200px;
      margin: 2rem auto;
      padding: 0 1rem;
    }
    h1 {
      text-align: center;
      font-size: 3rem;
      margin-bottom: 2rem;
      color: #4A7B8C;
    }
    .row {
      display: flex;
      gap: 2rem;
    }
    .panel {
      background: #222;
      border: 2px solid #4A7B8C;
      border-radius: 8px;
      display: flex;
      flex-direction: column;
      width: calc(50% - 1rem);  # 50% width minus gap
      box-shadow: 0 0 8px rgba(0,0,0,0.5);
      min-width: 0;
    }
    .panel header {
      background: #333;
      padding: .75rem 1rem;
      font-weight: bold;
      color: #EEE;
      border-bottom: 2px solid #4A7B8C;
      width: 100%;
    }
    .panel textarea {
      background: #111;
      border: 0.2px solid #4A7B8C;
      color: #CCC;
      padding: 1rem;
      font-family: monospace;
      font-size: 1rem;
      height: 650px;
      width: 100%;
      resize: vertical;
    }
    .panel textarea:focus {
      outline: 2px solid #4A7B8C;
    }
    .btn {
      display: block;
      width: 240px;
      margin: 2rem auto;
      background: #4A7B8C;
      color: #111;
      border: none;
      padding: .75rem;
      font-size: 1.1rem;
      font-weight: bold;
      border-radius: 4px;
      cursor: pointer;
      transition: background .3s;
    }
    .btn:hover {
      background: #6A9EAE;
    }
    .error-panel {
      background: #200;
      border: 1px solid #600;
      border-radius: 6px;
      padding: 1rem;
      margin-top: 1rem;
      color: #f88;
      font-family: monospace;
      white-space: pre-wrap;
    }
  </style>
</head>
<body>
  <div class="container">
    <h1>C to Promela Converter</h1>
    <form method="POST">
      <div class="row">
        <div class="panel">
          <header>Input</header>
          <textarea name="input_code" required placeholder="Paste your C code here…">{{ input_code }}</textarea>
        </div>
        <div class="panel">
          <header>Output</header>
          <textarea readonly placeholder="Promela output…">{{ output_code }}</textarea>
        </div>
      </div>
      <button type="submit" class="btn">Convert</button>
    </form>

    {% if checked %}
    <div class="error-panel">
      <strong>C Syntax Check:</strong><br>
      {% if c_errors %}{{ c_errors }}{% else %}No errors found in C code.{% endif %}
    </div>
    {% endif %}
  </div>
</body>
</html>
''' 
# ─── Flask Endpoint ───────────────────────────────────────────────────────────
@app.route('/', methods=['GET', 'POST'])
def index():
    input_code  = ''
    c_errors    = ''
    output_code = ''
    checked     = False

    if request.method == 'POST':
        checked = True
        input_code = request.form['input_code']

        # write to samples/main.c
        main_c = os.path.join(SAMPLES_DIR, 'main.c')
        with open(main_c, 'w') as f:
            f.write(input_code)

        # syntax check
        proc_c = subprocess.run([
            'gcc', '-fsyntax-only', 'samples/main.c'],
            cwd=BASE_DIR, capture_output=True, text=True
        )
        c_errors = proc_c.stderr.strip()

        # conversion if no errors
        if proc_c.returncode == 0:
            subprocess.run([
                sys.executable, '-m', 'c2p', 'samples/main.c', '-o', 'main.pml'],
                cwd=BASE_DIR, capture_output=True, text=True
            )
            if os.path.exists(PML_OUT):
                with open(PML_OUT) as f:
                    output_code = ''.join([ln for ln in f if ln.strip()])

    return render_template_string(
        HTML,
        input_code=input_code,
        c_errors=c_errors,
        output_code=output_code,
        checked=checked
    )

if __name__ == '__main__':
    app.run(debug=True)
