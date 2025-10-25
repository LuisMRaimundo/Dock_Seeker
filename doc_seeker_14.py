from PyPDF2 import PdfReader
try:
    from pdfminer.high_level import extract_text as pdfminer_extract_text
except Exception:
    pdfminer_extract_text = None

import scipy.stats
from scipy.stats import skew, kurtosis
from scipy.stats import entropy
import os
import re
import io
import sys
import hashlib
import unicodedata
import tempfile
from datetime import datetime
from pathlib import Path
from collections import defaultdict
from difflib import SequenceMatcher

# 📌 GUI (Tkinter) Imports (Used Only in GUI Mode)
from tkinter import Tk, filedialog, messagebox, ttk, N, S, E, W, StringVar, BooleanVar

# 📌 Flask (Web Interface)
from flask import Flask, request, jsonify, render_template, send_from_directory

# 📌 File Parsing & Document Handling
from PyPDF2 import PdfReader
from docx import Document
from bs4 import BeautifulSoup

# 📌 Optical Character Recognition (OCR)
import pytesseract

# 📌 Image Processing
from PIL import Image, ImageEnhance, ImageFilter
import numpy as np
from skimage import filters
import cv2
import html

# 📌 Configuração do Tesseract para Windows
import platform
if platform.system() == 'Windows':
    pytesseract.pytesseract.tesseract_cmd = r'D:\Tesseract\tesseract.exe'
    print("✅ Tesseract configurado para Windows")
import re, unicodedata

NORMALIZE_JOIN_LINEBREAKED_WORDS = True


def normalize_extracted_text(s: str) -> str:
    if not s:
        return s
    # ligaduras e unicodes invisíveis
    s = (s.replace("ﬁ", "fi").replace("ﬂ", "fl")
           .replace("ﬀ","ff").replace("ﬃ","ffi").replace("ﬄ","ffl").replace("ﬆ","st"))
    s = s.replace("\u00ad", "").replace("\u200b", "").replace("\u200c", "").replace("\u200d", "")
    # juntar palavras partidas COM hífen:  tex- \n ture  -> texture
    s = re.sub(r"([0-9A-Za-zÀ-ÖØ-öø-ÿ])-\s*\n\s*([0-9A-Za-zÀ-ÖØ-öø-ÿ])", r"\1\2", s, flags=re.UNICODE)
    if NORMALIZE_JOIN_LINEBREAKED_WORDS:
        # juntar palavras partidas SEM hífen:  tex \n ture -> texture
        s = re.sub(r"([A-Za-zÀ-ÖØ-öø-ÿ])\s*\n\s*([a-zà-öø-ÿ])", r"\1\2", s, flags=re.UNICODE)
    # restantes quebras → espaço
    s = re.sub(r"\s*\n\s*", " ", s)
    # colapsar espaços
    s = re.sub(r"[ \t]{2,}", " ", s)
    return s.strip()


def _wildcard_word_to_regex(word: str):
    """
    Converte 'word' com * e ? em regex com limites de palavra, unicode-safe.
    Ex.: harm* -> r'\bharm\w*\b'
    """
    pat = re.escape(word.lower())
    pat = pat.replace(r"\*", r"\w*").replace(r"\?", r"\w")
    return re.compile(r"\b" + pat + r"\b", flags=re.UNICODE | re.IGNORECASE)


def build_highlight_regexes(terms):
    """
    A partir dos search_terms (termos e frases), devolve regexes para highlight.
    Frases são realçadas palavra-a-palavra (robusto e simples).
    """
    rx_list, seen = [], set()
    for t in terms or []:
        t = (t or "").strip()
        if not t:
            continue
        words = t.split() if " " in t else [t]
        for w in words:
            rx = _wildcard_word_to_regex(w)
            if rx.pattern not in seen:
                seen.add(rx.pattern)
                rx_list.append(rx)
    return rx_list


def highlight_context_html(context: str, terms):
    """
    Constrói HTML com <span class="highlight">…</span> nos matches (wildcards/frases).
    Faz merge de overlaps e escapa corretamente.
    """
    if not context:
        return ""
    rx_list = build_highlight_regexes(terms)
    if not rx_list:
        return html.escape(context)

    spans = []
    for rx in rx_list:
        for m in rx.finditer(context):
            spans.append((m.start(), m.end()))
    if not spans:
        return html.escape(context)

    spans.sort()
    merged = []
    cur_s, cur_e = spans[0]
    for s, e in spans[1:]:
        if s <= cur_e:
            cur_e = max(cur_e, e)
        else:
            merged.append((cur_s, cur_e))
            cur_s, cur_e = s, e
    merged.append((cur_s, cur_e))

    out, last = [], 0
    for s, e in merged:
        if last < s:
            out.append(html.escape(context[last:s]))
        out.append('<span class="highlight">')
        out.append(html.escape(context[s:e]))
        out.append('</span>')
        last = e
    if last < len(context):
        out.append(html.escape(context[last:]))
    return "".join(out)


HELP_TEXT_BOOLEAN = """
AJUDA — Pesquisa booleana avançada

OPERADORES E PRECEDÊNCIA
- Operadores suportados (maiúsculas): NOT, NEAR/x, AND, OR
- Precedência (da mais alta para a mais baixa):  NOT > NEAR/x > AND > OR
- Associação: NOT é unário; os restantes são binários e left-associative.
- NÃO existe AND implícito. Escreve sempre AND/OR/NEAR explicitamente.

SINTAXE
- Palavras simples:  algoritmo  interoperabilidade
- Frases exatas entre aspas:  "sound mass"   "top-of-atmosphere radiance"
- Agrupamento com parênteses:  (A OR B) AND NOT C
- Proximidade:  termo1 NEAR/5 termo2    "frase A" NEAR/3 "frase B"
  • NEAR/x é insensível à ordem (A perto de B ou B perto de A).
  • A distância é medida em nº de palavras entre os inícios dos operandos.
- Wildcards em termos e em palavras dentro de frases:
  • *  corresponde a 0 ou mais caracteres alfanuméricos (unicode)
  • ?  corresponde a 1 carácter alfanumérico
  Exemplos:  harm*  uni?orm*  "massa * sonora"

HÍFENES E BARRAS (ROBUSTEZ)
- Em frases entre aspas, hífenes e barras contam como espaço:
    "top-of-atmosphere radiance" equivale a "top of atmosphere radiance"
    "ISO/TC 211" equivale a "ISO TC 211"
- Em termos simples com hífen/barra (sem aspas), o termo é dividido e
  exige-se a sequência contígua:  iso/tc → ["iso","tc"].

EXEMPLOS PRÁTICOS
1) Básicos
   - interoperab*                         (apanha interoperability, interoperable)
   - "Plain Language Summary"
   - "fiducial reference measurements"    (frase exata)

2) Proximidade NEAR/x
   - OGC NEAR/5 "ISO/TC 211"
   - observ* NEAR/15 algorithm*           (observação/observer ~ algoritmo(s))
   - "in-situ" NEAR/6 "ground-truth"

3) Combinações com AND/OR/NOT
   - (GCMD OR SWEET) AND ontology
   - ("in-situ" OR "in situ") AND (remote OR satellite)
   - "in-situ" AND NOT "ex-situ"

4) Hífen/barra em frases
   - "top-of-atmosphere radiance"
   - "ISO/TC 211" NEAR/5 thesaur*

5) Wildcards (em PT/EN)
   - organi?ation      (organization / organisation)
   - homogenis*        (homogenisation / homogenization)
   - "massa * sonora"  (palavra intermédia livre)

BOAS PRÁTICAS
- Define sempre AND/OR/NEAR entre termos; evita “listas soltas” de palavras.
- Usa aspas para conceitos compostos: "sound mass", "observation result".
- Usa wildcards para variantes:  observ*  (observação/observations/observer).
- Para NEAR/x, começa com x pequeno (3–6) e aumenta apenas se necessário.
- Em PDFs/OCR, testa ambas as grafias com/sem hífen: "in-situ" e "in situ".

NOTAS TÉCNICAS (IMPLEMENTAÇÃO)
- Case-insensitive e unicode: acentos/diacríticos são mantidos.
- Frases com hífen/barra são normalizadas internamente para espaços (apenas
  para matching/realce); não altera o texto original do documento.
- NEAR/x com frases mede a distância entre a 1.ª palavra de cada operando.
- Wildcards mapeiam-se a caracteres alfanuméricos (\\w):
    * → \\w*    ? → \\w
- NOT tem precedência máxima e aplica-se ao operando seguinte ou ( ... ).
- O realce (highlight) no HTML é feito por palavra (nas frases com wildcards).

TROUBLESHOOTING
- “Não encontro resultados com NOT”: NOT não aumenta o score; se usares muito
  NOT, baixa o “Minimum Relevance” (ex.: 0.0) para inspecionar os matches.
- “Frase com hífen não dá”: certifica-te que está entre aspas. No motor,
  "x-y z" ≈ "x y z".
- “NEAR/x mostra snippet longe do par”: a extração tenta centrar no par mais
  próximo; aumenta o window se o contexto for demasiado curto.
- “OCR com ruído”: ativa a normalização (de-hifenização) e testa sem acentos
  no termo (se o PDF tiver extração deficiente).

RESUMO RÁPIDO (CHEATSHEET)
- termos:         harmonia   textura
- frase:          "sound mass"
- wildcard:       harm*   uni?orm*
- hífen/frase:    "top-of-atmosphere radiance"  ==  "top of atmosphere radiance"
- proximidade:    A NEAR/5 B
- negação:        (A OR B) AND NOT C
- grupos:         (A OR B) AND (C NEAR/3 D)
"""


# ✅ Define Flask App **before** using @app.route
app = Flask(__name__)


def check_dependencies():
    """Verifica se todas as dependências necessárias estão instaladas"""
    missing_deps = []

    try:
        import cv2
    except ImportError:
        missing_deps.append("opencv-python")

    try:
        from skimage import filters
    except ImportError:
        missing_deps.append("scikit-image")

    try:
        import pytesseract
        # Testa se o Tesseract está acessível
        pytesseract.get_tesseract_version()
    except Exception as e:
        missing_deps.append("tesseract (executável não encontrado)")

    if missing_deps:
        print(f"AVISO: Dependências faltando: {', '.join(missing_deps)}")
        print("Instale com: pip install opencv-python scikit-image")
        return False
    return True


# Create templates directory if it doesn't exist
if not os.path.exists('templates'):
    os.makedirs('templates')

# Create the index.html template
index_html_content = '''<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Document Search Tool - Web Interface</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            max-width: 800px;
            margin: 0 auto;
            padding: 20px;
            background-color: #f5f5f5;
        }
        .container {
            background-color: white;
            padding: 30px;
            border-radius: 10px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
        }
        h1 {
            color: #333;
            text-align: center;
        }
        .form-group {
            margin-bottom: 20px;
        }
        label {
            display: block;
            font-weight: bold;
            margin-bottom: 5px;
            color: #555;
        }
        input[type="text"], input[type="number"], select {
            width: 100%;
            padding: 8px;
            border: 1px solid #ddd;
            border-radius: 4px;
            box-sizing: border-box;
        }
        .checkbox-group {
            display: flex;
            flex-wrap: wrap;
            gap: 15px;
            margin-top: 5px;
        }
        .checkbox-group label {
            font-weight: normal;
            display: flex;
            align-items: center;
        }
        .checkbox-group input[type="checkbox"] {
            margin-right: 5px;
        }
        button {
            background-color: #4CAF50;
            color: white;
            padding: 10px 20px;
            border: none;
            border-radius: 4px;
            cursor: pointer;
            font-size: 16px;
            width: 100%;
            margin-top: 10px;
        }
        button:hover {
            background-color: #45a049;
        }
        button:disabled {
            background-color: #cccccc;
            cursor: not-allowed;
        }
        #results {
            margin-top: 30px;
        }
        .error {
            color: red;
            margin-top: 10px;
        }
        .success {
            color: green;
            margin-top: 10px;
        }
        .loading {
            text-align: center;
            margin-top: 20px;
        }
        .advanced-options {
            background-color: #f9f9f9;
            padding: 15px;
            border-radius: 5px;
            margin-top: 20px;
        }
        .ocr-options {
            background-color: #f0f0ff;
            padding: 10px;
            border-radius: 5px;
            margin-top: 10px;
        }
    </style>
</head>
<body>
    <div class="container">
        <h1>Document Search Tool</h1>

        <form id="searchForm">
            <div class="form-group">
                <label for="directory">Directory Path:</label>
                <input type="text" id="directory" name="directory" required
                       placeholder="e.g., C:\\Documents or /home/user/documents">
            </div>

            <div class="form-group">
                <label for="query">Search Query:</label>
                <input type="text" id="query" name="query" required
                       placeholder='e.g., term1 AND term2 OR "exact phrase"'>
                <small>Use AND, OR, NOT, NEAR/x. Use quotes for exact phrases (e.g., "sound mass" NEAR/3 texture).</small>

            </div>

            <div class="form-group">
                <label>File Types:</label>
                <div class="checkbox-group">
                    <label><input type="checkbox" name="file_types" value="txt" checked> Text (.txt)</label>
                    <label><input type="checkbox" name="file_types" value="pdf" checked> PDF (.pdf)</label>
                    <label><input type="checkbox" name="file_types" value="docx" checked> Word (.docx)</label>
                    <label><input type="checkbox" name="file_types" value="html" checked> HTML (.html)</label>
                    <label><input type="checkbox" name="file_types" value="image" checked> Images</label>
                </div>
            </div>

            <div class="advanced-options">
                <h3>Advanced Options</h3>

                <div class="ocr-options">
                    <label for="ocr_mode">OCR Mode for PDFs:</label>
                    <select id="ocr_mode" name="ocr_mode">
                        <option value="auto">Auto (detect if needed)</option>
                        <option value="force">Force OCR (always use)</option>
                        <option value="never">Never use OCR</option>
                    </select>
                    <small>Auto mode will check if PDF has text and only use OCR if needed</small>
                </div>

                <div class="form-group">
                    <label for="min_relevance">Minimum Relevance Score (0.0-1.0):</label>
                    <input type="number" id="min_relevance" name="min_relevance"
                           min="0" max="1" step="0.1" value="0.1">
                </div>

                <div class="form-group">
                    <label for="context_size">Context Window Size:</label>
                    <input type="number" id="context_size" name="context_size"
                           min="50" max="500" value="150">
                </div>

                <div class="form-group">
                    <label>
                        <input type="checkbox" id="show_duplicates" name="show_duplicates">
                        Show Duplicate Results
                    </label>
                </div>
            </div>

            <button type="submit" id="searchButton">Search Documents</button>
        </form>

        <div id="message"></div>
        <div id="results"></div>
    </div>

    <script>
        document.getElementById('searchForm').addEventListener('submit', async (e) => {
            e.preventDefault();

            const button = document.getElementById('searchButton');
            const messageDiv = document.getElementById('message');
            const resultsDiv = document.getElementById('results');

            // Clear previous results
            messageDiv.innerHTML = '';
            resultsDiv.innerHTML = '';

            // Disable button and show loading
            button.disabled = true;
            button.textContent = 'Searching...';
            messageDiv.innerHTML = '<div class="loading">Searching documents, please wait...</div>';

            // Collect form data
            const formData = new FormData(e.target);
            const data = {
                directory: formData.get('directory'),
                query: formData.get('query'),
                file_types: formData.getAll('file_types'),
                ocr_mode: formData.get('ocr_mode'),
                min_relevance: parseFloat(formData.get('min_relevance')),
                context_size: parseInt(formData.get('context_size')),
                show_duplicates: formData.get('show_duplicates') ? true : false
            };

            try {
                // Send search request
                const response = await fetch('/search', {
                    method: 'POST',
                    headers: {
                        'Content-Type': 'application/json',
                    },
                    body: JSON.stringify(data)
                });

                // Check if response is JSON
                const contentType = response.headers.get("content-type");
                if (!contentType || !contentType.includes("application/json")) {
                    throw new TypeError("Server didn't return JSON!");
                }

                const result = await response.json();

                if (result.status === 'success') {
                    messageDiv.innerHTML = `<div class="success">Found ${result.total_results} results!</div>`;
                    resultsDiv.innerHTML = result.results_html;

                    // Add download button
                    if (result.results_file) {
                        const filename = result.results_file.split(/[\\\\/]/).pop();
                        messageDiv.innerHTML += `
                            <a href="/download-results/${filename}"
                               download="search_results.html"
                               style="display: inline-block; margin-top: 10px;
                                      padding: 5px 10px; background-color: #2196F3;
                                      color: white; text-decoration: none;
                                      border-radius: 4px;">
                                Download Results
                            </a>`;
                    }
                } else {
                    messageDiv.innerHTML = `<div class="error">Error: ${result.message}</div>`;
                }
            } catch (error) {
                console.error('Error:', error);
                messageDiv.innerHTML = `<div class="error">Error: ${error.message}</div>`;
            } finally {
                // Re-enable button
                button.disabled = false;
                button.textContent = 'Search Documents';
            }
        });
    </script>
</body>
</html>'''

# Write the template file
with open('templates/index.html', 'w', encoding='utf-8') as f:
    f.write(index_html_content)

print("Web interface template created successfully!")

# ✅ Web API Route (Defined **after** app initialization)


@app.route("/search", methods=["POST"])
def search():
    """Handle search requests via Web interface with improved results"""
    try:
        data = request.json

        # Validate required fields
        if not data.get("query"):
            return jsonify({
                "status": "error",
                "message": "Search query is required"
            }), 400

        if not data.get("directory"):
            return jsonify({
                "status": "error",
                "message": "Directory path is required"
            }), 400

        # Check if directory exists
        if not os.path.exists(data.get("directory")):
            return jsonify({
                "status": "error",
                "message": f"Directory not found: {data.get('directory')}"
            }), 400

        search_query = data.get("query", "")
        directory = data.get("directory", "")
        file_types = {}

        # Convert file types from the request
        for ft in ['txt', 'pdf', 'docx', 'html', 'image']:
            file_types[ft] = ft in data.get("file_types", [])

        # Get additional parameters with defaults
        min_relevance = float(data.get("min_relevance", 0.1))
        context_size = int(data.get("context_size", 150))
        show_duplicates = data.get("show_duplicates", False)
        ocr_mode = data.get("ocr_mode", "auto")  # NEW: Get OCR mode

        # Perform the search
        results = search_in_files(
            directory,
            search_query,
            file_types,
            min_relevance=min_relevance,
            context_size=context_size,
            ocr_mode=ocr_mode  # NEW: Pass OCR mode
        )

        # Create temporary file for results
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        temp_dir = tempfile.gettempdir()
        output_file = os.path.join(
            temp_dir, f"search_results_{timestamp}.html")

        # Save results to HTML file
        save_results(output_file, results,
                     show_duplicates=show_duplicates, output_format="html")

        # Read the HTML content back
        with open(output_file, 'r', encoding='utf-8') as f:
            html_content = f.read()

        # Create a formatted JSON response
        response_data = {
            "status": "success",
            "total_results": len(results),
            "results_html": html_content,
            "results_file": output_file
        }

        return jsonify(response_data)

    except Exception as e:
        import traceback
        print(f"Error in search route: {str(e)}")
        print(traceback.format_exc())
        return jsonify({
            "status": "error",
            "message": str(e)
        }), 500


@app.route("/")
def index():
    """Serve the improved search interface"""
    return render_template("index.html")


@app.route("/download-results/<filename>")
def download_results(filename):
    """Allow downloading of the results file"""
    temp_dir = tempfile.gettempdir()
    return send_from_directory(
        temp_dir,
        filename,
        as_attachment=True,
        download_name="search_results.html"
    )


@app.errorhandler(404)
def not_found(error):
    return jsonify({
        "status": "error",
        "message": "Endpoint not found"
    }), 404


@app.errorhandler(500)
def internal_error(error):
    return jsonify({
        "status": "error",
        "message": "Internal server error"
    }), 500


class ContentHash:
    def __init__(self):
        self.seen_hashes = {}

    def is_duplicate(self, content, filepath):
        """Check if content is duplicate and store hash if not"""
        # Create hash of content
        content_hash = hashlib.md5(content.encode('utf-8')).hexdigest()

        if content_hash in self.seen_hashes:
            original_file = self.seen_hashes[content_hash]
            print(
                f"Duplicate content detected: {filepath} matches {original_file}")
            return True

        self.seen_hashes[content_hash] = filepath
        return False


class SearchResult:
    def __init__(self, filepath, query, location, context, relevance_score=0.0, snippet_start=0, snippet_end=0, search_terms=None):
        self.filepath = filepath
        self.query = query
        self.location = location
        self.context = context
        self.relevance_score = relevance_score
        self.snippet_start = snippet_start
        self.snippet_end = snippet_end
        self.search_terms = search_terms or []


class BooleanSearchParser:
    """
    Parser/avaliador booleando com suporte a:
      - AND, OR, NOT (NOT unário)
      - NEAR/x (x >= 0; binário; distância em nº de palavras)
      - Parênteses e aspas para frases
    Precedências: NOT > NEAR/x > AND > OR (todas left-assoc., exceto NOT)
    """

    def __init__(self, query):
        self.original_query = query.strip()
        self.query = self._normalize_text(query.strip())
        # tokens para o shunting-yard preservam aspas para distinguir frase
        self.tokens = self._tokenize(self.query)
        self.rpn = self._to_rpn(self.tokens)  # Reverse Polish Notation
        # termos simples (sem operadores) usados na pontuação/contexto
        self.search_terms = self._extract_terms_for_scoring(self.tokens)

    def is_simple_query(self):
        """
        Verifica se a consulta é simples (apenas um termo ou frase, sem operadores).
        """
        if not self.tokens:
            return False
        # Uma consulta simples não tem operadores (AND, OR, NOT, NEAR) nem parênteses.
        for token in self.tokens:
            if self._is_operator(token) or token in ('(', ')'):
                return False
        return True

    def find_all_term_occurrences(self, text):
        """
        Encontra todas as ocorrências de um termo/frase simples e retorna seus spans.
        """
        if not self.is_simple_query() or not self.search_terms:
            return []

        term = self.search_terms[0]
        text_norm = self._normalize_text(text).lower()
        spans = []

        if " " in term:
            # Lógica para frases (simplificada para regex)
            phrase_regex = self._wildcard_to_regex(term.replace(" ", r'\s+'))
            rx = re.compile(phrase_regex, flags=re.UNICODE | re.IGNORECASE)
        else:
            # Lógica para termos únicos
            rx = re.compile(self._wildcard_to_regex(term), flags=re.UNICODE | re.IGNORECASE)

        for match in rx.finditer(text_norm):
            spans.append((match.start(), match.end()))

        return spans

    def extract_context_at_span(self, text, start, end, window_size):
        """
        Extrai um snippet de contexto em torno de um span (início, fim) específico.
        """
        center = (start + end) // 2
        half_window = window_size // 2

        context_start = max(0, center - half_window)
        context_end = min(len(text), center + half_window)

        snippet = text[context_start:context_end]

        if context_start > 0:
            snippet = "... " + snippet
        if context_end < len(text):
            snippet = snippet + " ..."

        return snippet, context_start, context_end

    def max_near_k(self):
        """Maior x pedido em NEAR/x na query (default 1)."""
        k_max = 1
        for t in self.tokens:
            if isinstance(t, str) and t.upper().startswith('NEAR/'):
                parts = t.split('/')
                if len(parts) == 2 and parts[1].isdigit():
                    k_max = max(k_max, int(parts[1]))
        return k_max

    # ---------- Interface pública ----------
    def evaluate(self, text):
        """Retorna (matches: bool, score: float)"""
        if not self.rpn:
            return False, 0.0
        words = self._split_words(text)  # lista de palavras (lower), para NEAR
        match = self._eval_rpn(self.rpn, text, words)
        if match:
            score = self.calculate_relevance_score(text, 0, len(text))
            return True, score
        return False, 0.0

    def extract_context(self, text, window_size=150):
        """
        Extrai um excerto centrado:
          - Se a query tiver NEAR/x: centra no PAR de termos/frases mais próximo.
          - Caso contrário: centra na 1.ª ocorrência de QUALQUER termo/frase,
            respeitando wildcards (*, ?) e frases com hífen/barra.
        Devolve (snippet, start_char, end_char).
        """
        import re

        if not text:
            return "", 0, 0

        # Normalização (de-hifenização, soft-hyphen, etc.)
        try:
            text = normalize_extracted_text(text)
        except Exception:
            pass

        # ---------- util: mapear palavras -> offsets ----------
        def _word_spans(t):
            t_norm = self._normalize_text(t)
            spans = [(m.group(0).lower(), m.start(), m.end())
                     for m in re.finditer(r"\w+", t_norm, flags=re.UNICODE)]
            words = [w for (w, s, e) in spans]
            return t_norm, words, spans

        text_norm, words_lower, spans = _word_spans(text)
        if not words_lower:
            end = min(len(text_norm), window_size)
            return text_norm[:end], 0, end

        # Há NEAR/x na query?
        has_near = any(isinstance(tok, str) and tok.upper(
        ).startswith("NEAR/") for tok in self.tokens)

        # ---------- Caso NEAR/x: centrar no par mais próximo ----------
        if has_near:
            term_list = []
            for t in (self.search_terms or []):
                tt = (t or "").strip()
                if not tt:
                    continue
                if " " in tt:
                    # frase (hífen/barra/wildcard-aware)
                    pos = self._positions_for_phrase(words_lower, tt)
                else:
                    tok = self._normalize_word(tt)
                    pos = self._positions_for_token(
                        words_lower, tok)  # termo (wildcard-aware)
                if pos:
                    term_list.append((tt, pos))

            best = None  # (dist, i_idx, j_idx)
            for i in range(len(term_list)):
                pa = sorted(term_list[i][1])
                for j in range(i + 1, len(term_list)):
                    pb = sorted(term_list[j][1])
                    ia = ib = 0
                    while ia < len(pa) and ib < len(pb):
                        d = abs(pa[ia] - pb[ib])
                        if (best is None) or (d < best[0]):
                            best = (d, pa[ia], pb[ib])
                            if best[0] == 0:
                                break
                        if pa[ia] < pb[ib]:
                            ia += 1
                        else:
                            ib += 1
                    if best and best[0] == 0:
                        break
                if best and best[0] == 0:
                    break

            if best is not None:
                i_word = min(best[1], best[2])
                j_word = max(best[1], best[2])
                start_char = spans[i_word][1]
                end_char_pair = spans[j_word][2]
                center = (start_char + end_char_pair) // 2
                start = max(0, center - window_size)
                end = min(len(text_norm), center + window_size)
                snippet = text_norm[start:end].strip()
                if start > 0:
                    snippet = "… " + snippet
                if end < len(text_norm):
                    snippet = snippet + " …"
                return snippet, start, end
            # senão, cai no fallback abaixo

        # ---------- Fallback: 1.ª ocorrência (wildcard + hífen/barra-aware) ----------
        rx_list, seen = [], set()
        for term in (self.search_terms or []):
            t = (term or "").strip()
            if not t:
                continue
            if " " in t:
                # frase: hífen/barra -> espaço; múltiplos espaços -> 1
                t_norm = self._normalize_text(t).lower()
                t_norm = re.sub(r"[-–—/]+", " ", t_norm)
                t_norm = re.sub(r"\s+", " ", t_norm).strip()
                parts = [p for p in t_norm.split(" ") if p]
                for p in parts:
                    pat = self._wildcard_to_regex(p)  # \b...\b com * e ?
                    if pat not in seen:
                        seen.add(pat)
                        rx_list.append(re.compile(
                            pat, flags=re.UNICODE | re.IGNORECASE))
            else:
                if any(ch in t for ch in "-–—/"):
                    subs = [p for p in re.split(r"[-–—/]+", t) if p]
                    for p in subs:
                        pat = self._wildcard_to_regex(p)
                        if pat not in seen:
                            seen.add(pat)
                            rx_list.append(re.compile(
                                pat, flags=re.UNICODE | re.IGNORECASE))
                else:
                    pat = self._wildcard_to_regex(t)
                    if pat not in seen:
                        seen.add(pat)
                        rx_list.append(re.compile(
                            pat, flags=re.UNICODE | re.IGNORECASE))

        hit_index = None
        hit_len = 0
        for rx in rx_list:
            m = rx.search(text_norm)
            if m and ((hit_index is None) or (m.start() < hit_index)):
                hit_index = m.start()
                hit_len = m.end() - m.start()

        if hit_index is None:
            start = 0
            end = min(len(text_norm), window_size)
            snippet = text_norm[start:end].strip()
            return snippet, start, end

        start = max(0, hit_index - window_size)
        end = min(len(text_norm), hit_index + hit_len + window_size)
        snippet = text_norm[start:end].strip()
        if start > 0:
            snippet = "… " + snippet
        if end < len(text_norm):
            snippet = snippet + " …"
        return snippet, start, end

        # se não encontrou pares válidos, cai no fallback abaixo.

        # ---------- Fallback: 1.ª ocorrência de QUALQUER termo, com wildcard ----------
        # Construir regexes para procurar a 1ª ocorrência (wildcards incluídos).
        # Para frases: tornamos hífen/barra em espaço e realçamos palavra-a-palavra.
        rx_list = []
        seen = set()
        for term in (self.search_terms or []):
            t = (term or "").strip()
            if not t:
                continue
            if " " in t:
                # frase: hífen/barra -> espaço; múltiplos espaços -> 1
                t_norm = self._normalize_text(t).lower()
                t_norm = re.sub(r"[-–—/]+", " ", t_norm)
                t_norm = re.sub(r"\s+", " ", t_norm).strip()
                parts = [p for p in t_norm.split(" ") if p]
                for p in parts:
                    pat = self._wildcard_to_regex(p)  # \b...\b com * e ?
                    if pat not in seen:
                        seen.add(pat)
                        rx_list.append(re.compile(
                            pat, flags=re.UNICODE | re.IGNORECASE))
            else:
                # termo simples: se tiver hífen/barra, divide em subpalavras contíguas
                if any(ch in t for ch in "-–—/"):
                    sub = [p for p in re.split(r"[-–—/]+", t) if p]
                    for p in sub:
                        pat = self._wildcard_to_regex(p)
                        if pat not in seen:
                            seen.add(pat)
                            rx_list.append(re.compile(
                                pat, flags=re.UNICODE | re.IGNORECASE))
                else:
                    pat = self._wildcard_to_regex(t)
                    if pat not in seen:
                        seen.add(pat)
                        rx_list.append(re.compile(
                            pat, flags=re.UNICODE | re.IGNORECASE))

        # Procurar a 1ª ocorrência de qualquer regex
        hit_index = None
        hit_len = 0
        for rx in rx_list:
            m = rx.search(text_norm)
            if m:
                if (hit_index is None) or (m.start() < hit_index):
                    hit_index = m.start()
                    hit_len = m.end() - m.start()

        if hit_index is None:
            # nenhum termo encontrado: devolve início
            start = 0
            end = min(len(text_norm), window_size)
            snippet = text_norm[start:end].strip()
            return snippet, start, end

        start = max(0, hit_index - window_size)
        end = min(len(text_norm), hit_index + hit_len + window_size)
        snippet = text_norm[start:end].strip()
        if start > 0:
            snippet = "… " + snippet
        if end < len(text_norm):
            snippet = snippet + " …"
        return snippet, start, end

    # ---------- Tokenização ----------

    def _tokenize(self, q):
        tokens = []
        i, n = 0, len(q)
        WHITESPACE = set(' \t\r\n')
        while i < n:
            c = q[i]

            if c in '()':
                tokens.append(c)
                i += 1
                continue

            if c in WHITESPACE:
                i += 1
                continue

            # Frases entre aspas
            if c in ['"', "'"]:
                quote = c
                i += 1
                start = i
                buf = []
                while i < n and q[i] != quote:
                    buf.append(q[i])
                    i += 1
                if i < n and q[i] == quote:
                    i += 1  # consumir a aspa final
                tokens.append(f'"{"".join(buf)}"')
                continue

            # Operador NEAR/x (com espaço opcional)
            if q[i:i+5].upper() == 'NEAR/':
                i += 5
                # Pular espaços em branco após a barra
                while i < n and q[i] in WHITESPACE:
                    i += 1

                num_start = i
                while i < n and q[i].isdigit():
                    i += 1

                if num_start < i:
                    tokens.append(f'NEAR/{q[num_start:i]}')
                else:
                    # Fallback se não houver número
                    tokens.append('NEAR/1')
                continue

            # Palavras/operadores AND|OR|NOT
            buf = []
            while i < n and q[i] not in WHITESPACE and q[i] not in '()':
                # parar antes de NEAR/ sem consumir
                if q[i:i+5].upper() == 'NEAR/':
                    break
                buf.append(q[i])
                i += 1
            token = ''.join(buf).strip()

            if not token:
                continue

            up = token.upper()
            if up in ('AND', 'OR', 'NOT'):
                tokens.append(up)
            else:
                # termo (palavra única) ou sequência sem aspas
                tokens.append(token)
        # Inserção implícita de AND? — NÃO. Mantemos sem heurística para rigor.
        return tokens

    # ---------- Shunting-yard (infix -> RPN) ----------
    def _precedence(self, op):
        if isinstance(op, str) and op.upper().startswith('NEAR/'):
            return 3
        if op == 'NOT':
            return 4
        if op == 'AND':
            return 2
        if op == 'OR':
            return 1
        return 0

    def _is_operator(self, tok):
        if tok in ('AND', 'OR', 'NOT'):
            return True
        if isinstance(tok, str) and tok.upper().startswith('NEAR/'):
            # validar NEAR/x
            parts = tok.split('/')
            return len(parts) == 2 and parts[0].upper() == 'NEAR' and parts[1].isdigit()
        return False

    def _to_rpn(self, tokens):
        output, stack = [], []
        i, n = 0, len(tokens)
        while i < n:
            t = tokens[i]

            if t == '(':
                stack.append(t)

            elif t == ')':
                while stack and stack[-1] != '(':
                    output.append(stack.pop())
                if stack and stack[-1] == '(':
                    stack.pop()
                else:
                    # parêntese desalinhado: ignorar silenciosamente
                    pass

            elif self._is_operator(t):
                # NOT é unário (right-assoc por convenção aqui)
                while stack and self._is_operator(stack[-1]):
                    top = stack[-1]
                    if (t != 'NOT' and self._precedence(top) >= self._precedence(t)) or \
                       (t == 'NOT' and self._precedence(top) > self._precedence(t)):
                        output.append(stack.pop())
                    else:
                        break
                stack.append(t)

            else:
                # operando (termo ou "frase")
                output.append(t)

            i += 1

        while stack:
            output.append(stack.pop())
        return output

    # ---------- Avaliação em RPN ----------
    def _eval_rpn(self, rpn, full_text, words_lower):
        """
        words_lower: lista de tokens (apenas letras/números), já em lower
        """
        stack = []
        for t in rpn:
            if not self._is_operator(t) and t not in ('(', ')'):
                # (bool, positions)
                stack.append(self._eval_operand(t, full_text, words_lower))
                continue

            if t == 'NOT':
                if not stack:
                    stack.append((False, []))
                else:
                    b, _pos = stack.pop()
                    stack.append((not b, []))
                continue

            # binários: AND, OR, NEAR/x
            if len(stack) < 2:
                # expressão malformada -> falso
                return False
            right_b, right_pos = stack.pop()
            left_b, left_pos = stack.pop()

            if t == 'AND':
                stack.append((left_b and right_b, []))
            elif t == 'OR':
                stack.append((left_b or right_b, []))
            elif t.upper().startswith('NEAR/'):
                k = int(t.split('/')[1]) if t.split('/')[1].isdigit() else 1
                # se qualquer operando for falso, NEAR é falso
                if not (left_b and right_b):
                    stack.append((False, []))
                else:
                    near_ok = self._proximity_within_k(left_pos, right_pos, k)
                    stack.append((near_ok, []))
            else:
                return False

        return bool(stack and stack[-1][0])

    # ---------- Operandos/posições ----------
    def _eval_operand(self, operand, full_text, words_lower):
        """
        Retorna (bool, positions) onde positions é lista de índices de palavras
        que marcam a 'ocorrência' do operando (para NEAR/x).
        operand pode ser "frase com espaços" (se veio com aspas) ou termo simples.
        """
        is_phrase = len(operand) >= 2 and (
            (operand[0] == operand[-1] ==
             '"') or (operand[0] == operand[-1] == "'")
        )
        if is_phrase:
            content = operand[1:-1].strip()
            pos = self._positions_for_phrase(words_lower, content)
            return (len(pos) > 0, pos)
        else:
            token = self._normalize_word(operand)
            if not token:
                return (False, [])
            pos = self._positions_for_token(words_lower, token)
            return (len(pos) > 0, pos)

    # --- SUBSTITUIR NA TUA CLASSE BooleanSearchParser ---

    def _positions_for_token(self, words_lower, token):
        """
        Casa um termo simples:
          - com wildcard (*, ?) → regex por palavra
          - hífen/barra → divide e exige sequência contígua (ex.: 'iso/tc' → ['iso','tc'])
          - caso normal → igualdade por palavra
        """
        import re
        # wildcard
        if self._is_wildcard(token):
            rx = re.compile(self._wildcard_to_regex(token), flags=re.UNICODE)
            return [i for i, w in enumerate(words_lower) if rx.search(w)]

        # hífenes / barras: tratar como sequência contígua de subpalavras
        if any(ch in token for ch in "-–—/"):
            parts = [p for p in re.split(r"[-–—/]+", token) if p]
            if not parts:
                return []
            m = len(parts)
            hits = []
            for i in range(0, len(words_lower) - m + 1):
                ok = True
                for j in range(m):
                    if words_lower[i + j] != parts[j]:
                        ok = False
                        break
                if ok:
                    hits.append(i)
            return hits

        # literal
        return [i for i, w in enumerate(words_lower) if w == token]

    def _positions_for_phrase(self, words_lower, phrase_text):
        """
        Frases entre aspas:
          - normaliza (lower, NFKC)
          - torna hífenes/barra equivalentes a espaço (ex.: "top-of-atmosphere" → "top of atmosphere")
          - suporta wildcards por palavra
          - exige sequência contígua
        """
        import re
        # normalizar e tornar hífenes/barras em espaço
        norm = self._normalize_text(phrase_text).lower()
        norm = re.sub(r"[-–—/]+", " ", norm)
        norm = re.sub(r"\s+", " ", norm).strip()

        parts = [p for p in norm.split(" ") if p]
        m = len(parts)
        if m == 0:
            return []
        if m == 1:
            # delega para token (já trata wildcard e hífen/barras num termo)
            return self._positions_for_token(words_lower, parts[0])

        # compilar “padrões” por palavra (string literal ou regex se wildcard)
        comp = []
        for p in parts:
            if self._is_wildcard(p):
                comp.append(re.compile(
                    self._wildcard_to_regex(p), flags=re.UNICODE))
            else:
                comp.append(p)

        hits = []
        # varrer janelas contíguas de m palavras
        for i in range(0, len(words_lower) - m + 1):
            ok = True
            for j in range(m):
                wj = words_lower[i + j]
                pj = comp[j]
                if isinstance(pj, str):
                    if wj != pj:
                        ok = False
                        break
                else:
                    if not pj.search(wj):
                        ok = False
                        break
            if ok:
                hits.append(i)
        return hits

    def _proximity_within_k(self, pos_a, pos_b, k):
        """
        Verdadeiro se existir |i - j| <= k para i em pos_a, j em pos_b
        (k=0 permite mesma posição; usual é k>=1)
        """
        if not pos_a or not pos_b:
            return False
        ia, ib = 0, 0
        pos_a_sorted = sorted(pos_a)
        pos_b_sorted = sorted(pos_b)
        while ia < len(pos_a_sorted) and ib < len(pos_b_sorted):
            da = pos_a_sorted[ia] - pos_b_sorted[ib]
            if abs(da) <= k:
                return True
            if da < 0:
                ia += 1
            else:
                ib += 1
        return False

    # ---------- Utilidades de texto ----------
    def _split_words(self, text):
        # tokens estritamente alfanuméricos, lower; preserva acentuação via NFKC
        t = self._normalize_text(text).lower()
        return re.findall(r'\w+', t, flags=re.UNICODE)

    def _normalize_word(self, w):
        return self._normalize_text(w).lower()

    def _normalize_text(self, text):
        return unicodedata.normalize('NFKC', text)

    # ---------- Termos para scoring/contexto ----------
    def _extract_terms_for_scoring(self, tokens):
        terms = []
        for t in tokens:
            if t in ('AND', 'OR', 'NOT'):
                continue
            if isinstance(t, str) and t.upper().startswith('NEAR/'):
                continue
            # remover aspas para scoring
            if len(t) >= 2 and ((t[0] == t[-1] == '"') or (t[0] == t[-1] == "'")):
                terms.append(t[1:-1])
            else:
                terms.append(t)
        # deduplicar mantendo ordem
        seen = set()
        out = []
        for z in terms:
            key = z.lower()
            if key not in seen:
                seen.add(key)
                out.append(z)
        return out

        # ---------- Wildcards ----------

    def _is_wildcard(self, s: str) -> bool:
        return ('*' in s) or ('?' in s)

    def _wildcard_to_regex(self, pat: str) -> str:
        """
        Converte um termo com * e ? num padrão regex, unicode-safe, para casar PALAVRAS.
        - *  -> \w*
        - ?  -> \w
        Aplica limites de palavra \b…\b.
        Ex.: "harm*" -> r"\bharm\w*\b"
             "?mass" -> r"\b\wmass\b"
        """
        import re
        # normalizar e escapar tudo, depois reintroduzir curingas
        esc = re.escape(pat.lower())
        esc = esc.replace(r'\*', r'\w*').replace(r'\?', r'\w')
        return r'\b' + esc + r'\b'

    # ---------- Reaproveita scoring original ----------
    def calculate_relevance_score(self, text, start=0, end=None):
        """
        Score baseado em contagem de ocorrências:
          - termo simples: peso 1.0 por ocorrência
          - frase (>=2 palavras): peso 2.0 por ocorrência
        Usa as funções de posição (que já suportam wildcards) para garantir
        consistência entre match e scoring.
        """
        if end is None:
            end = len(text)
        segment = self._normalize_text(text[start:end])
        words = self._split_words(segment)
        if not self.search_terms:
            return 0.0

        score = 0.0
        for term in self.search_terms:
            t = (term or "").strip()
            if not t:
                continue
            if " " in t:
                cnt = len(self._positions_for_phrase(words, t))
                score += 2.0 * cnt
            else:
                token = self._normalize_word(t)
                cnt = len(self._positions_for_token(words, token))
                score += 1.0 * cnt

        # normalização simples pela extensão do segmento
        L = max(1, len(segment))
        norm = 1000.0 / (1000.0 + L)
        return score * norm


def save_results(output_file, results, show_duplicates=False, output_format="html"):
    """Save search results with enhanced formatting and hyperlinks to document locations.
    Depende de: normalize_extracted_text, highlight_context_html, BooleanSearchParser.
    Se não existirem, faz fallback seguro (sem highlight).
    """
    # Validação do formato
    if output_format not in ["txt", "html"]:
        print(
            f"Warning: Invalid output format '{output_format}'. Defaulting to 'txt'.")
        output_format = "txt"

    # Ajustar extensão
    if output_format == "html" and not output_file.lower().endswith('.html'):
        output_file = os.path.splitext(output_file)[0] + '.html'

    with open(output_file, 'w', encoding='utf-8', errors='replace') as f:
        # Cabeçalho HTML
        if output_format == "html":
            f.write("""<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Document Search Results</title>
    <style>
        body { font-family: Arial, sans-serif; line-height: 1.6; margin: 20px; }
        .header, .footer { background-color: #f5f5f5; padding: 10px; border-radius: 5px; }
        .summary { background-color: #e9f7fe; padding: 10px; margin: 15px 0; border-radius: 5px; }
        .file { border: 1px solid #ddd; margin: 20px 0; padding: 10px; border-radius: 5px; }
        .file-header { background-color: #f0f0f0; padding: 10px; margin-bottom: 15px; }
        .match { border-left: 4px solid #4CAF50; padding-left: 10px; margin: 15px 0; }
        .context { background-color: #f9f9f9; padding: 15px; border-radius: 5px; white-space: pre-wrap; }
        .highlight { background-color: #FFFF00; font-weight: bold; }
        hr { border: 0; border-top: 1px solid #ddd; margin: 20px 0; }
        a { color: #0066cc; text-decoration: none; }
        a:hover { text-decoration: underline; }
        .score { color: #666; font-style: italic; }
        .file-actions { margin-top: 10px; }
        .btn-open-file {
            display: inline-block;
            padding: 5px 10px;
            background-color: #4CAF50;
            color: white;
            border-radius: 4px;
            text-decoration: none;
            margin-right: 10px;
        }
        .btn-copy-path {
            display: inline-block;
            padding: 5px 10px;
            background-color: #2196F3;
            color: white;
            border-radius: 4px;
            text-decoration: none;
            cursor: pointer;
        }
        .os-path {
            font-family: monospace;
            background: #f8f8f8;
            padding: 2px 5px;
            border: 1px solid #ddd;
            border-radius: 3px;
        }
    </style>
    <script>
        function copyToClipboard(text) {
            navigator.clipboard.writeText(text)
                .then(() => { alert('Path copied to clipboard!'); })
                .catch(err => { console.error('Error copying text: ', err); });
        }
        function openWithDefaultApp(filePath, pageNum) {
            if (pageNum && filePath.toLowerCase().endsWith('.pdf')) {
                const link = document.createElement('a');
                link.href = 'file://' + filePath + '#page=' + pageNum;
                link.target = '_blank';
                document.body.appendChild(link);
                link.click();
                document.body.removeChild(link);
                return;
            }
            const confirmOpen = confirm('Open this file with the default application?\\n' + filePath);
            if (confirmOpen) {
                const link = document.createElement('a');
                link.href = 'file://' + filePath;
                link.target = '_blank';
                document.body.appendChild(link);
                link.click();
                document.body.removeChild(link);
            }
        }
    </script>
</head>
<body>
""")

        # Cabeçalho comum
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        if output_format == "html":
            f.write('<div class="header">\n')
            f.write('<h1>Document Search Results</h1>\n')
            f.write(f'<p>Generated: {timestamp}</p>\n')
            f.write('</div>\n')
        else:
            f.write("=" * 80 + "\n")
            f.write(f"DOCUMENT SEARCH RESULTS - Generated: {timestamp}\n")
            f.write("=" * 80 + "\n\n")

        # Summary
        unique_files = len(set(r.filepath for r in results))
        unique_queries = len(set(r.query for r in results))
        if output_format == "html":
            f.write('<div class="summary">\n<h2>Summary</h2>\n<ul>\n')
            f.write(
                f'  <li><strong>Total Matches:</strong> {len(results)}</li>\n')
            f.write(
                f'  <li><strong>Unique Files:</strong> {unique_files}</li>\n')
            f.write(
                f'  <li><strong>Search Queries:</strong> {unique_queries}</li>\n')
            f.write('</ul>\n</div>\n')
        else:
            f.write("SUMMARY:\n")
            f.write(f"  Total Matches: {len(results)}\n")
            f.write(f"  Unique Files: {unique_files}\n")
            f.write(f"  Search Queries: {unique_queries}\n")
            f.write("-" * 80 + "\n\n")

        # Agrupar por ficheiro, removendo duplicados de snippet+query
        grouped_results = defaultdict(list)
        seen_content = set()
        for r in results:
            key = (r.context, r.query)
            if not show_duplicates and key in seen_content:
                continue
            seen_content.add(key)
            grouped_results[r.filepath].append(r)

        # Ordenar ficheiros por melhor score
        sorted_files = sorted(
            grouped_results.items(),
            key=lambda kv: max(x.relevance_score for x in kv[1]),
            reverse=True
        )

        system = platform.system()

        # Render por ficheiro
        for file_num, (filepath, file_results) in enumerate(sorted_files, 1):
            filename = os.path.basename(filepath)
            directory = os.path.dirname(filepath)
            abs_path = os.path.abspath(filepath)
            file_uri = f"file://{abs_path.replace(' ', '%20')}"

            if output_format == "html":
                f.write(f'<div class="file" id="file-{file_num}">\n')
                f.write('<div class="file-header">\n')
                f.write(f'<h2>File #{file_num}: {filename}</h2>\n')
                f.write(f'<p><strong>Location:</strong> {directory}</p>\n')
                if system == "Windows":
                    formatted_path = abs_path.replace('\\', '\\\\')
                else:
                    formatted_path = abs_path
                f.write(
                    f'<p><strong>Full Path:</strong> <span class="os-path">{abs_path}</span></p>\n')
                f.write('<div class="file-actions">\n')
                f.write(
                    f'  <a href="javascript:void(0)" onclick="openWithDefaultApp(\'{formatted_path}\', null)" class="btn-open-file">Open File</a>\n')
                f.write(
                    f'  <a href="javascript:void(0)" onclick="copyToClipboard(\'{formatted_path}\')" class="btn-copy-path">Copy Path</a>\n')
                f.write('</div>\n</div>\n')
            else:
                f.write(f"FILE #{file_num}: {filename}\n")
                f.write(f"  Location: {directory}\n")
                f.write(f"  Full Path: {filepath}\n")
                f.write(f"  Link: {file_uri}\n")
                f.write("-" * 80 + "\n")

            # Ordenar matches
            file_results.sort(key=lambda x: x.relevance_score, reverse=True)

            # Matches
            for match_num, r in enumerate(file_results, 1):
                # Label de posição
                if filepath.lower().endswith(".pdf"):
                    location_label = f"Page {r.location}"
                    position_param = f"{r.location}"
                elif filepath.lower().endswith(".docx"):
                    location_label = f"Paragraph {r.location}"
                    position_param = ""
                elif filepath.lower().endswith((".html", ".htm")):
                    location_label = f"Element {r.location}"
                    position_param = ""
                else:
                    location_label = f"Line {r.location}"
                    position_param = ""

                if output_format == "html":
                    f.write(
                        f'<div class="match" id="match-{file_num}-{match_num}">\n')
                    f.write(
                        f'<h3>Match #{match_num} <span class="score">[Score: {r.relevance_score:.2f}]</span></h3>\n')
                    if filepath.lower().endswith(".pdf") and position_param:
                        f.write(
                            f'<p><strong>Position:</strong> {location_label} ')
                        f.write(
                            f'<a href="javascript:void(0)" onclick="openWithDefaultApp(\'{formatted_path}\', {position_param})">(Open to Page)</a></p>\n')
                    else:
                        f.write(
                            f'<p><strong>Position:</strong> {location_label}</p>\n')
                    f.write(f'<p><strong>Query:</strong> "{r.query}"</p>\n')

                    # --- Normalização do snippet ---
                    try:
                        context_text = normalize_extracted_text(
                            r.context or "")
                    except Exception:
                        context_text = r.context or ""

                    # --- Highlight robusto (wildcards/frases) ---
                    try:
                        parser_for_highlight = BooleanSearchParser(
                            getattr(r, "query", "") or "")
                        terms = getattr(parser_for_highlight,
                                        "search_terms", []) or []
                        context_html = highlight_context_html(
                            context_text, terms)
                    except Exception:
                        # fallback: sem highlight
                        context_html = html.escape(context_text)

                    f.write(f'<div class="context">{context_html}</div>\n')
                    f.write('</div>\n')
                else:
                    f.write(
                        f"\n  MATCH #{match_num} [Score: {r.relevance_score:.2f}]\n")
                    f.write(f"  Position: {location_label}\n")
                    if filepath.lower().endswith(".pdf") and position_param:
                        f.write(f"  Link: {file_uri}#page={position_param}\n")
                    else:
                        f.write(f"  Link: {file_uri}\n")
                    f.write(f"  Query: \"{r.query}\"\n\n")
                    # Normalizar e embrulhar texto
                    try:
                        ctx = normalize_extracted_text(r.context or "")
                    except Exception:
                        ctx = r.context or ""
                    f.write("  " + "-" * 70 + "\n")
                    f.write("  CONTEXT:\n")
                    words = ctx.split()
                    line = "    "
                    for w in words:
                        if len(line) + len(w) + 1 > 74:
                            f.write(line + "\n")
                            line = "    " + w
                        else:
                            line += (" " if line.strip() else "") + w
                    if line.strip():
                        f.write(line + "\n")
                    f.write("  " + "-" * 70 + "\n")

            if output_format == "html":
                f.write('</div>\n')
            else:
                f.write("\n" + "=" * 80 + "\n\n")

        # Rodapé
        if output_format == "html":
            f.write("""<div class="footer">
    <p>Search complete. Results are sorted by relevance score (higher = better match).</p>
    <p>Highlighted terms indicate the matched search terms.</p>
    <p>Click "Open File" to open the document, or "Copy Path" to copy the file path to clipboard.</p>
    <p>For PDF files, you can open directly to the specific page.</p>
</div>

<script>
    // Fix for Firefox which blocks direct file:// links
    document.addEventListener('DOMContentLoaded', function() {
        if (navigator.userAgent.includes('Firefox')) {
            const fileLinks = document.querySelectorAll('a[href^="file://"]');
            fileLinks.forEach(link => {
                const originalHref = link.getAttribute('href');
                link.setAttribute('data-href', originalHref);
                link.setAttribute('href', 'javascript:void(0)');
                link.addEventListener('click', function() {
                    alert('Firefox blocks direct file:// links. Please copy the path and open the file manually.');
                    copyToClipboard(originalHref.replace('file://', ''));
                });
            });
        }
    });
</script>
</body>
</html>""")
        else:
            f.write("SEARCH COMPLETE\n")
            f.write("-" * 80 + "\n")
            f.write(
                "Note: Results are sorted by relevance score (higher = better match).\n")
            f.write("      Matches are highlighted with ** around search terms.\n")
            f.write(
                "      Some applications may not open file:// links directly for security reasons.\n")


def pdf_has_text(filepath):
    """Check if a PDF has extractable text (not a scanned image)"""
    try:
        reader = PdfReader(filepath)
        for page in reader.pages[:3]:  # Check first 3 pages as sample
            text = page.extract_text()
            if text and text.strip() and len(text.strip()) > 50:  # More than 50 chars indicates real text
                return True
        return False
    except Exception as e:
        print(f"Error checking PDF text: {e}")
        return False


def search_in_text_file(filepath, boolean_parser, context_size):
    """Refactored search for text files."""
    results = []
    raw = None
    for enc in ("utf-8-sig", "utf-8", "utf-16", "latin-1"):
        try:
            with open(filepath, "r", encoding=enc, errors="ignore") as fh:
                raw = fh.read()
            if raw:
                break
        except Exception:
            continue
    if not raw:
        print(f"Error reading text file {filepath}: empty/decoding failed")
        return results

    text = normalize_extracted_text(raw)

    if boolean_parser.is_simple_query():
        spans = boolean_parser.find_all_term_occurrences(text)
        for start, end in spans:
            context, s, e = boolean_parser.extract_context_at_span(text, start, end, context_size)
            score = boolean_parser.calculate_relevance_score(context, 0, len(context))

            line_no = 1
            try:
                probe = context.lstrip("… ").rstrip(" …")[:80]
                idx = raw.lower().find(probe.lower())
                if idx != -1:
                    line_no = raw.count("\n", 0, idx) + 1
            except Exception:
                pass

            results.append(SearchResult(
                filepath=filepath,
                query=boolean_parser.original_query,
                location=line_no,
                context=context,
                relevance_score=score,
                snippet_start=s,
                snippet_end=e
            ))
    else:
        # Fallback to original logic for complex queries
        matches, score = boolean_parser.evaluate(text)
        if matches:
            context, s, e = boolean_parser.extract_context(text, context_size)
            score = boolean_parser.calculate_relevance_score(context, 0, len(context))
            results.append(SearchResult(
                filepath=filepath,
                query=boolean_parser.original_query,
                location=1,
                context=context,
                relevance_score=score,
                snippet_start=s,
                snippet_end=e
            ))

    return results


def search_in_pdf_file(filepath, boolean_parser, context_size, ocr_mode="auto"):
    """
    Search in PDF files with OCR mode control

    OCR Modes:
    - "auto": Check if PDF has text, use OCR only if needed
    - "force": Always use OCR regardless of text presence
    - "never": Never use OCR, only extract existing text
    """
    results = []
    try:
        print(f"\nProcessing PDF: {filepath}")
        print(f"OCR Mode: {ocr_mode}")

        # Determine if we should use OCR
        use_ocr = False
        has_text = False

        if ocr_mode == "force":
            use_ocr = True
            print("OCR forced - will use OCR on all pages")
        elif ocr_mode == "never":
            use_ocr = False
            print("OCR disabled - will only extract existing text")
        else:  # auto mode
            has_text = pdf_has_text(filepath)
            use_ocr = not has_text
            print(
                f"Auto mode - PDF has text: {has_text}, will use OCR: {use_ocr}")

        reader = PdfReader(filepath)
        print(f"Total pages found: {len(reader.pages)}")

        for page_num, page in enumerate(reader.pages, 1):
            try:
                text = ""

                # Try normal text extraction first (unless forcing OCR)
                if ocr_mode != "force":
                    extracted = page.extract_text()
                    if extracted and extracted.strip():
                        text = extracted
                        print(
                            f"Page {page_num}: Extracted {len(text)} characters of raw text")

                # Use OCR if configured and needed
                if use_ocr and (not text.strip() or ocr_mode == "force"):
                    if ocr_mode == "never":
                        print(
                            f"Page {page_num}: No text found, but OCR is disabled")
                        continue

                    print(f"Page {page_num}: Using OCR.")
                    try:
                        from pdf2image import convert_from_path  # may raise ImportError
                        images = convert_from_path(
                            filepath, first_page=page_num, last_page=page_num)
                        if images:
                            ocr_text = extract_text_from_image(images[0])
                            if ocr_text:
                                text = ocr_text
                                print(
                                    f"Page {page_num}: OCR extracted {len(text)} characters")
                        else:
                            print(
                                f"Page {page_num}: Failed to convert to image")
                    except ImportError:
                        print("Warning: pdf2image not installed, OCR unavailable")
                        print("Install with: pip install pdf2image")
                        # fall through; if no text, we won't match
                    except Exception as e:
                        print(f"Page {page_num}: OCR error - {str(e)}")

                # >>> NORMALIZAÇÃO ANTES DE AVALIAR <<<
                if text and text.strip():
                    norm = normalize_extracted_text(text)
                    if boolean_parser.is_simple_query():
                        spans = boolean_parser.find_all_term_occurrences(norm)
                        for start, end in spans:
                            context, s, e = boolean_parser.extract_context_at_span(norm, start, end, context_size)
                            score = boolean_parser.calculate_relevance_score(context, 0, len(context))
                            results.append(SearchResult(
                                filepath=filepath,
                                query=boolean_parser.original_query,
                                location=page_num,
                                context=context,
                                relevance_score=score,
                                snippet_start=s,
                                snippet_end=e
                            ))
                    else:
                        matches, score = boolean_parser.evaluate(norm)
                        if matches:
                            print(
                                f"Page {page_num}: Match found with score: {score}")
                            context, start, end = boolean_parser.extract_context(
                                norm, context_size)
                            results.append(SearchResult(
                                filepath=filepath,
                                query=boolean_parser.original_query,
                                location=page_num,
                                context=context,
                                relevance_score=score,
                                snippet_start=start,
                                snippet_end=end
                            ))

            except Exception as e:
                print(f"Error processing page {page_num}: {str(e)}")
                continue

    except Exception as e:
        print(f"Error reading PDF file: {str(e)}")

    print(f"Results found for this PDF: {len(results)}")
    return results


def search_in_docx_file(filepath, boolean_parser, context_size):
    """Search in Word documents with context tracking"""
    results = []
    try:
        doc = Document(filepath)
        for para_num, paragraph in enumerate(doc.paragraphs, 1):
            raw = paragraph.text
            if raw:
                text = normalize_extracted_text(raw)
                if boolean_parser.is_simple_query():
                    spans = boolean_parser.find_all_term_occurrences(text)
                    for start, end in spans:
                        context, s, e = boolean_parser.extract_context_at_span(text, start, end, context_size)
                        score = boolean_parser.calculate_relevance_score(context, 0, len(context))
                        results.append(SearchResult(
                            filepath=filepath,
                            query=boolean_parser.original_query,
                            location=para_num,
                            context=context,
                            relevance_score=score,
                            snippet_start=s,
                            snippet_end=e
                        ))
                else:
                    matches, score = boolean_parser.evaluate(text)
                    if matches:
                        context, start, end = boolean_parser.extract_context(
                            text, context_size)
                        results.append(SearchResult(
                            filepath=filepath,
                            query=boolean_parser.original_query,
                            location=para_num,
                            context=context,
                            relevance_score=score,
                            snippet_start=start,
                            snippet_end=end
                        ))
    except Exception as e:
        print(f"Error reading DOCX file {filepath}: {e}")
    return results


def search_in_html_file(filepath, boolean_parser, context_size):
    """Search in HTML with sliding window of elements (robusto para NEAR/x entre elementos)."""
    results = []
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as file:
            soup = BeautifulSoup(file, 'html.parser')
            for tag in soup(["script", "style"]):
                tag.decompose()
            text = normalize_extracted_text(soup.get_text())

            if not text:
                return results

            if boolean_parser.is_simple_query():
                spans = boolean_parser.find_all_term_occurrences(text)
                for start, end in spans:
                    context, s, e = boolean_parser.extract_context_at_span(text, start, end, context_size)
                    score = boolean_parser.calculate_relevance_score(context, 0, len(context))
                    results.append(SearchResult(
                        filepath=filepath,
                        query=boolean_parser.original_query,
                        location=1,
                        context=context,
                        relevance_score=score,
                        snippet_start=s,
                        snippet_end=e
                    ))
            else:
                matches, score = boolean_parser.evaluate(text)
                if matches:
                    context, s, e = boolean_parser.extract_context(
                        text, context_size)

                    results.append(SearchResult(
                        filepath=filepath,
                        query=boolean_parser.original_query,
                        location=1,  # Simplified for HTML
                        context=context,
                        relevance_score=score,
                        snippet_start=s,
                        snippet_end=e
                    ))
    except Exception as e:
        print(f"Error reading HTML file {filepath}: {e}")
    return results


def search_in_image_file(filepath, boolean_parser, context_size):
    """Search in images using OCR with context tracking"""
    results = []
    print(f"\n{'='*60}")
    print(f"🔍 Processando arquivo de imagem: {filepath}")
    print(f"📏 Tamanho do arquivo: {os.path.getsize(filepath) / 1024:.2f} KB")

    try:
        raw = extract_text_from_image(filepath)
        if raw:
            text = normalize_extracted_text(raw)
            print(
                f"✅ Texto extraído com sucesso. Tamanho: {len(text)} caracteres")
            print(f"🔎 Procurando por: '{boolean_parser.original_query}'")

            if boolean_parser.is_simple_query():
                spans = boolean_parser.find_all_term_occurrences(text)
                for start, end in spans:
                    context, s, e = boolean_parser.extract_context_at_span(text, start, end, context_size)
                    score = boolean_parser.calculate_relevance_score(context, 0, len(context))
                    results.append(SearchResult(
                        filepath=filepath,
                        query=boolean_parser.original_query,
                        location=1,
                        context=context,
                        relevance_score=score,
                        snippet_start=s,
                        snippet_end=e
                    ))
            else:
                matches, score = boolean_parser.evaluate(text)
                if matches:
                    print(f"🎯 MATCH ENCONTRADO! Score: {score:.2f}")
                    context, start, end = boolean_parser.extract_context(
                        text, context_size)
                    results.append(SearchResult(
                        filepath=filepath,
                        query=boolean_parser.original_query,
                        location=1,
                        context=context,
                        relevance_score=score,
                        snippet_start=start,
                        snippet_end=end
                    ))
        else:
            print("⚠️ AVISO: Nenhum texto foi extraído da imagem")

    except Exception as e:
        print(f"❌ ERRO ao processar imagem {filepath}: {e}")
        import traceback
        traceback.print_exc()

    print(f"📊 Resultados encontrados: {len(results)}")
    print(f"{'='*60}\n")
    return results


def preprocess_image(image):
    """Preprocess image to improve OCR accuracy using advanced techniques."""
    try:
        # Converter para escala de cinza se necessário
        if image.mode != 'L':
            image = image.convert('L')

        # Aumentar o contraste
        enhancer = ImageEnhance.Contrast(image)
        image = enhancer.enhance(3.0)

        # Converter para array NumPy para OpenCV
        img_array = np.array(image)

        # Aplicar desfoque gaussiano para redução de ruído
        img_array = cv2.GaussianBlur(img_array, (3, 3), 0)

        # Aplicar CLAHE (Contrast Limited Adaptive Histogram Equalization)
        clahe = cv2.createCLAHE(clipLimit=3.0, tileGridSize=(8, 8))
        img_array = clahe.apply(img_array)

        # Aplicar um filtro bilateral
        img_array = cv2.bilateralFilter(img_array, 5, 75, 75)

        # Aplicar binarização Otsu
        _, binary = cv2.threshold(
            img_array, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)

        # Aplicar operações morfológicas
        kernel = np.ones((1, 1), np.uint8)
        binary = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel)

        # Converter de volta para imagem PIL
        return Image.fromarray(binary)

    except Exception as e:
        print(f"Erro ao processar a imagem: {e}")
        return image


def deskew_image(image):
    """Detect and correct skew in an image using OpenCV."""
    try:
        # Convert PIL image to numpy array (grayscale)
        img_array = np.array(image.convert('L'))

        # Apply thresholding to obtain a binary image
        _, binary = cv2.threshold(
            img_array, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)

        # Find non-zero pixel coordinates
        coords = np.column_stack(np.where(binary > 0))

        # Compute the angle of the text
        angle = cv2.minAreaRect(coords)[-1]

        # Adjust angle
        if angle < -45:
            angle = 90 + angle
        else:
            angle = -angle

        # Get image dimensions
        (h, w) = img_array.shape[:2]
        center = (w // 2, h // 2)

        # Compute rotation matrix
        M = cv2.getRotationMatrix2D(center, angle, 1.0)

        # Apply affine transformation to correct skew
        rotated = cv2.warpAffine(
            img_array, M, (w, h), flags=cv2.INTER_CUBIC, borderMode=cv2.BORDER_REPLICATE)

        # Convert back to PIL image
        return Image.fromarray(rotated)

    except Exception as e:
        print(f"Error deskewing image: {e}")
        return image


def extract_text_from_pdf(path: str, ocr_mode="auto") -> list[str]:
    """
    Extrai texto por página com pdfminer.six (se disponível); se falhar/der vazio,
    tenta PyPDF2; se ainda vazio e OCR ativo, usa OCR por página.
    """
    pages: list[str] = []
    # 1) pdfminer.six (melhor cobertura)
    if pdfminer_extract_text is not None:
        try:
            full = pdfminer_extract_text(path) or ""
            # pdfminer separa páginas por form-feed
            raw_pages = re.split(r" ", full)
            if raw_pages:
                pages = raw_pages
        except Exception:
            pages = []
    # 2) fallback PyPDF2 por página
    if not pages:
        try:
            reader = PdfReader(path)
            for p in reader.pages:
                t = p.extract_text() or ""
                pages.append(t)
        except Exception:
            pages = []
    # 3) OCR por página vazia (se ativo)
    if ocr_mode != "off":
        for i, t in enumerate(pages):
            if not t or len(t.strip()) < 5:
                try:
                    # Import here to avoid global dependency if not used
                    from pdf2image import convert_from_path
                    # Convert only the specific page to an image
                    images = convert_from_path(
                        path, first_page=i + 1, last_page=i + 1)
                    if images:
                        ocr_text = extract_text_from_image(images[0])
                        pages[i] = ocr_text or ""
                except ImportError:
                    print("Warning: pdf2image not installed. OCR will not be available in 'extract_text_from_pdf'.")
                    # Stop trying if the dependency is missing
                    break
                except Exception as e:
                    print(f"Error during OCR on page {i+1} of {path}: {e}")
                    # Continue to the next page
    return pages




def extract_text_from_image(image_input):
    """
    Enhanced text extraction from images using preprocessing and configured OCR.
    Accepts either a file path or a PIL Image object.
    """
    try:
        print(
            f"\n🖼️ Iniciando extração de texto de: {image_input if isinstance(image_input, str) else 'PIL Image object'}")

        # Garantir que o Tesseract está configurado
        if platform.system() == 'Windows' and not pytesseract.pytesseract.tesseract_cmd:
            pytesseract.pytesseract.tesseract_cmd = r'C:\Program Files\Tesseract-OCR\tesseract.exe'

        # Verificar se o Tesseract está acessível
        try:
            version = pytesseract.get_tesseract_version()
            print(f"✅ Tesseract {version} está funcionando")
        except Exception as e:
            print(f"❌ ERRO: Tesseract não está acessível: {e}")
            return ""

        # Se for um caminho, abrir a imagem
        if isinstance(image_input, str):
            if not os.path.exists(image_input):
                print(f"❌ Arquivo não encontrado: {image_input}")
                return ""
            image = Image.open(image_input)
            print(f"✅ Imagem carregada: {image.size}, modo: {image.mode}")
        elif isinstance(image_input, Image.Image):
            image = image_input
        else:
            raise ValueError("Invalid image input type")

        # Converter para RGB se necessário
        if image.mode != 'RGB':
            image = image.convert('RGB')
            print(f"📋 Imagem convertida para RGB")

        # Verificar idiomas disponíveis
        try:
            langs = pytesseract.get_languages(config='')
            print(f"🌐 Idiomas disponíveis: {langs}")

            # Usar apenas idiomas que estão instalados
            lang_list = []
            for lang in ['eng', 'por']:
                if lang in langs:
                    lang_list.append(lang)

            lang_param = '+'.join(lang_list) if lang_list else 'eng'
            print(f"📝 Usando idiomas: {lang_param}")
        except:
            lang_param = 'eng'

        # Pré-processamento
        print("🔧 Aplicando pré-processamento...")
        processed_image = preprocess_image(image)

        # Configuração do OCR
        custom_config = r'--oem 3 --psm 3 -c preserve_interword_spaces=1'

        print("🔍 Executando OCR...")
        text = pytesseract.image_to_string(
            processed_image,
            config=custom_config,
            lang=lang_param
        )

        # Se não encontrou texto, tentar sem pré-processamento
        if not text.strip():
            print(
                "⚠️ Nenhum texto encontrado com pré-processamento, tentando imagem original...")
            text = pytesseract.image_to_string(image, lang=lang_param)

        # Pós-processamento do texto
        if text:
            text = re.sub(r'\s+', ' ', text)
            text = ''.join(
                char for char in text if char.isprintable() or char in '\n\t')
            print(
                f"✅ Texto extraído com sucesso! Tamanho: {len(text)} caracteres")
            print(f"📄 Preview: {text[:200]}...")
            return text.strip()
        else:
            print("❌ Nenhum texto foi extraído da imagem")
            return ""

    except Exception as e:
        print(f"❌ ERRO ao processar imagem: {e}")
        import traceback
        traceback.print_exc()
        return ""


def search_in_files(directory, boolean_query, file_types, min_relevance=0.1, context_size=150, ocr_mode="auto"):
    """
    Main search function that coordinates the search across all file types

    Parameters:
    - directory: Directory to search in
    - boolean_query: Search query with boolean operators
    - file_types: Dict of file types to search
    - min_relevance: Minimum relevance score
    - context_size: Size of context window
    - ocr_mode: OCR mode for PDFs ("auto", "force", "never")
    """
    results = []
    boolean_parser = BooleanSearchParser(boolean_query)
    content_hash = ContentHash()

    print(f"\n🔍 Starting search with OCR mode: {ocr_mode}")

    for root, _, files in os.walk(directory):
        for file in files:
            filepath = os.path.join(root, file)
            lower_file = file.lower()

            try:
                if lower_file.endswith('.txt') and file_types['txt']:
                    results.extend(search_in_text_file(
                        filepath, boolean_parser, context_size))
                elif lower_file.endswith('.pdf') and file_types['pdf']:
                    # Pass OCR mode to PDF search
                    results.extend(search_in_pdf_file(
                        filepath, boolean_parser, context_size, ocr_mode))
                elif lower_file.endswith('.docx') and file_types['docx']:
                    results.extend(search_in_docx_file(
                        filepath, boolean_parser, context_size))
                elif lower_file.endswith(('.html', '.htm')) and file_types['html']:
                    results.extend(search_in_html_file(
                        filepath, boolean_parser, context_size))
                elif lower_file.endswith(('.png', '.jpg', '.jpeg', '.tiff', '.bmp')) and file_types['image']:
                    results.extend(search_in_image_file(
                        filepath, boolean_parser, context_size))
            except Exception as e:
                print(f"Error processing file {filepath}: {e}")
                continue

    # Filter results by relevance score and remove duplicates
    if boolean_parser.is_simple_query():
        filtered_results = [res for res in results if res.relevance_score >= min_relevance]
    else:
        filtered_results = []
        seen_content = set()

        for result in results:
            if result.relevance_score >= min_relevance:
                # Create a unique key for the content
                content_key = (result.context, result.query)

                # Check if this is duplicate content
                if not content_hash.is_duplicate(result.context, result.filepath):
                    if content_key not in seen_content:
                        seen_content.add(content_key)
                        filtered_results.append(result)

    # Sort results by relevance score
    filtered_results.sort(key=lambda x: x.relevance_score, reverse=True)

    return filtered_results


def run_interface():
    def select_directory():
        directory = filedialog.askdirectory(
            title="Select Directory with Documents")
        directory_var.set(directory)

    def select_output_file():
        file_path = filedialog.asksaveasfilename(
            title="Select Output File",
            defaultextension=".html",
            filetypes=[
                ("HTML Files", "*.html"),
                ("Text Files", "*.txt"),
                ("All Files", "*.*")
            ]
        )

        # Ensure the file has an extension
        if file_path and not os.path.splitext(file_path)[1]:
            file_path += ".html"

        output_file_var.set(file_path)

    def show_help():
        messagebox.showinfo("Boolean Search Help", HELP_TEXT_BOOLEAN)

        """
            Sintaxe de pesquisa booleana:
            - Operadores: AND, OR, NOT, NEAR/x   (maiúsculas)
            - Precedência:  NOT > NEAR/x > AND > OR
            - Parênteses para agrupar
            - Aspas para frases exatas

            NEAR/x:
            - Exige que os dois termos ocorram a uma distância ≤ x palavras.
              Ex.:   harmonia NEAR/3 textura
                     "massa sonora" NEAR/2 Ligeti
            - NEAR/1 ~ termos adjacentes (uma palavra de separação no máximo).

            Exemplos:
              term1 AND term2
              (term1 OR term2) AND NOT term3
              "exact phrase" NEAR/5 conceito
              (XENAKIS NEAR/2 textura) OR (Ligeti NEAR/3 micropolyphony)

            OCR (PDF):
            - Auto: usa OCR apenas se o PDF não tiver texto embebido
            - Force: força OCR em todas as páginas (mais lento)
            - Never: nunca usa OCR

            Wildcards:
            - * (0+ chars) e ? (1 char) dentro de termos/frases.
              Ex.: harm* ; uni?orm* ; "massa * sonora"

            Dicas:
            - Use aspas para conceitos compostos ("sound mass", "massa sonora").
            - Combine NEAR/x para captar proximidade sem impor ordem.
            """

    messagebox.showinfo("Boolean Search Help", HELP_TEXT_BOOLEAN)

    def start_search():
        directory = directory_var.get()
        output_file = output_file_var.get()
        search_query = terms_var.get()
        min_relevance = float(relevance_var.get())
        context_size = int(context_var.get())
        show_duplicates = show_duplicates_var.get()
        ocr_mode = ocr_mode_var.get()  # Get OCR mode

        file_types = {
            'txt': txt_var.get(),
            'pdf': pdf_var.get(),
            'docx': docx_var.get(),
            'html': html_var.get(),
            'image': image_var.get()
        }

        if not directory:
            messagebox.showerror("Error", "No directory selected.")
            return
        if not output_file:
            messagebox.showerror("Error", "No output file selected.")
            return
        if not search_query:
            messagebox.showerror("Error", "No search query provided.")
            return

        # Determine output format based on file extension
        if output_file.lower().endswith('.txt'):
            output_format = "txt"
        else:
            output_format = "html"

        try:
            # Update status bar
            status_var.set(f"Searching... (OCR Mode: {ocr_mode})")
            root.update_idletasks()

            results = search_in_files(directory, search_query, file_types,
                                      min_relevance=min_relevance,
                                      context_size=context_size,
                                      ocr_mode=ocr_mode)

            if results:
                # Save results with explicit format
                save_results(output_file, results,
                             show_duplicates=show_duplicates,
                             output_format=output_format)

                # Update status and show results
                status_var.set(
                    f"Search complete. Found {len(results)} results.")
                messagebox.showinfo("Results Found",
                                    f"Found {len(results)} results.\nSaved to: {output_file}\nFormat: {output_format.upper()}")
            else:
                status_var.set("Search complete. No results found.")
                messagebox.showinfo(
                    "No Results", "No matches found for the given query.")
        except Exception as e:
            status_var.set("Error occurred during search.")
            messagebox.showerror("Error", f"An error occurred: {str(e)}")

    # Initialize Tkinter GUI
    root = Tk()
    root.title("Enhanced Document Search Tool - v6 Improved")
    root.geometry("700x950")

    # Style configuration
    style = ttk.Style()
    style.configure('TFrame', padding=5)
    style.configure('Header.TLabel', font=('TkDefaultFont', 10, 'bold'))
    style.configure('Accent.TButton', font=('TkDefaultFont', 10, 'bold'))

    # Main frame
    main_frame = ttk.Frame(root, padding="10")
    main_frame.grid(row=0, column=0, sticky=(N, W, E, S))
    root.columnconfigure(0, weight=1)
    root.rowconfigure(0, weight=1)

    # Variables
    directory_var = StringVar()
    output_file_var = StringVar()
    terms_var = StringVar()
    txt_var = BooleanVar(value=True)
    pdf_var = BooleanVar(value=True)
    docx_var = BooleanVar(value=True)
    html_var = BooleanVar(value=True)
    image_var = BooleanVar(value=True)
    relevance_var = StringVar(value="0.1")
    context_var = StringVar(value="150")
    show_duplicates_var = BooleanVar(value=False)
    ocr_mode_var = StringVar(value="auto")  # NEW: OCR mode variable
    status_var = StringVar(value="Ready to search.")

    # Directory selection
    ttk.Label(main_frame, text="Directory:", style='Header.TLabel').grid(
        column=0, row=0, sticky=W)
    ttk.Button(main_frame, text="Select Directory",
               command=select_directory).grid(column=1, row=0, pady=5)
    ttk.Label(main_frame, textvariable=directory_var, wraplength=500).grid(
        column=0, row=1, columnspan=2, sticky=W)

    # Output file selection
    ttk.Label(main_frame, text="Output File:", style='Header.TLabel').grid(
        column=0, row=2, sticky=W, pady=(10, 0))
    ttk.Button(main_frame, text="Select Output File",
               command=select_output_file).grid(column=1, row=2, pady=5)
    ttk.Label(main_frame, textvariable=output_file_var, wraplength=500).grid(
        column=0, row=3, columnspan=2, sticky=W)

    # Search query
    ttk.Label(main_frame, text="Boolean Search Query:", style='Header.TLabel').grid(
        column=0, row=4, sticky=W, pady=(10, 0))
    ttk.Entry(main_frame, textvariable=terms_var, width=60).grid(
        column=0, row=5, columnspan=2, sticky=(W, E), pady=5)
    ttk.Button(main_frame, text="Search Help", command=show_help).grid(
        column=0, row=6, sticky=W)

    # Advanced options frame
    advanced_frame = ttk.LabelFrame(
        main_frame, text="Advanced Options", padding="5")
    advanced_frame.grid(column=0, row=7, columnspan=2, sticky=(W, E), pady=10)

    # OCR Mode selection (NEW)
    ttk.Label(advanced_frame, text="OCR Mode for PDFs:").grid(
        column=0, row=0, sticky=W)
    ocr_frame = ttk.Frame(advanced_frame)
    ocr_frame.grid(column=1, row=0, sticky=W, padx=5)
    ttk.Radiobutton(ocr_frame, text="Auto", variable=ocr_mode_var,
                    value="auto").pack(side="left")
    ttk.Radiobutton(ocr_frame, text="Force OCR", variable=ocr_mode_var,
                    value="force").pack(side="left", padx=10)
    ttk.Radiobutton(ocr_frame, text="Never",
                    variable=ocr_mode_var, value="never").pack(side="left")

    # Relevance score threshold
    ttk.Label(advanced_frame, text="Minimum Relevance Score (0.0-1.0):").grid(
        column=0, row=1, sticky=W, pady=(5, 0))
    ttk.Entry(advanced_frame, textvariable=relevance_var,
              width=10).grid(column=1, row=1, sticky=W, padx=5)

    # Context window size
    ttk.Label(advanced_frame, text="Context Window Size (characters):").grid(
        column=0, row=2, sticky=W, pady=5)
    ttk.Entry(advanced_frame, textvariable=context_var,
              width=10).grid(column=1, row=2, sticky=W, padx=5)

    # Show duplicates option
    ttk.Checkbutton(advanced_frame, text="Show Duplicate Results",
                    variable=show_duplicates_var).grid(column=0, row=3, columnspan=2, sticky=W)

    # File type selection frame
    file_type_frame = ttk.LabelFrame(
        main_frame, text="File Types to Search", padding="5")
    file_type_frame.grid(column=0, row=8, columnspan=2, sticky=(W, E), pady=10)

    ttk.Checkbutton(file_type_frame, text="Text Files (.txt)",
                    variable=txt_var).grid(column=0, row=0, sticky=W)
    ttk.Checkbutton(file_type_frame, text="PDF Files (.pdf)",
                    variable=pdf_var).grid(column=0, row=1, sticky=W)
    ttk.Checkbutton(file_type_frame, text="Word Files (.docx)",
                    variable=docx_var).grid(column=0, row=2, sticky=W)
    ttk.Checkbutton(file_type_frame, text="HTML Files (.html, .htm)",
                    variable=html_var).grid(column=0, row=3, sticky=W)
    ttk.Checkbutton(file_type_frame, text="Image Files (.png, .jpg, .jpeg, .tiff, .bmp)",
                    variable=image_var).grid(column=0, row=4, sticky=W)

    # Search button
    ttk.Button(main_frame, text="Start Search", command=start_search,
               style='Accent.TButton').grid(column=0, row=9, columnspan=2, pady=20)

    # Status bar
    status_bar = ttk.Label(
        main_frame, textvariable=status_var, relief='sunken')
    status_bar.grid(column=0, row=10, columnspan=2, sticky=(W, E))

    # Configure grid weights
    main_frame.columnconfigure(1, weight=1)

    # Add padding to all children
    for child in main_frame.winfo_children():
        child.grid_configure(padx=5)

    for child in advanced_frame.winfo_children():
        child.grid_configure(padx=5)

    for child in file_type_frame.winfo_children():
        child.grid_configure(padx=5)

    root.mainloop()


def test_ocr_functionality(test_image_path=None):
    """Função para testar a funcionalidade OCR isoladamente"""
    print("\n" + "="*60)
    print("🧪 TESTE DE FUNCIONALIDADE OCR")
    print("="*60 + "\n")

    # Verificar dependências
    print("1️⃣ Verificando dependências...")
    if not check_dependencies():
        print("❌ Dependências faltando! Instale-as antes de continuar.")
        return

    # Verificar Tesseract
    print("\n2️⃣ Verificando Tesseract...")
    try:
        version = pytesseract.get_tesseract_version()
        print(f"✅ Tesseract versão: {version}")
        langs = pytesseract.get_languages(config='')
        print(f"✅ Idiomas instalados: {langs}")
    except Exception as e:
        print(f"❌ Erro com Tesseract: {e}")
        return

    # Criar imagem de teste se não foi fornecida
    if not test_image_path:
        print("\n3️⃣ Criando imagem de teste...")
        from PIL import Image, ImageDraw, ImageFont

        img = Image.new('RGB', (400, 200), color='white')
        draw = ImageDraw.Draw(img)

        # Texto de teste
        test_text = "TESTE OCR\nDocSeeker v6\nPython OCR Test\n12345"

        try:
            # Tentar usar fonte Arial
            font = ImageFont.truetype("arial.ttf", 36)
        except:
            # Usar fonte padrão
            font = ImageFont.load_default()

        draw.text((50, 50), test_text, fill='black', font=font)

        # Salvar imagem temporária
        test_image_path = 'teste_ocr_temp.png'
        img.save(test_image_path)
        print(f"✅ Imagem de teste criada: {test_image_path}")

    # Testar extração
    print("\n4️⃣ Testando extração de texto...")
    extracted_text = extract_text_from_image(test_image_path)

    if extracted_text:
        print(f"\n✅ SUCESSO! Texto extraído:")
        print("-" * 40)
        print(extracted_text)
        print("-" * 40)
    else:
        print("\n❌ FALHA: Nenhum texto foi extraído")

    # Limpar arquivo temporário se foi criado
    if test_image_path == 'teste_ocr_temp.png' and os.path.exists(test_image_path):
        os.remove(test_image_path)
        print("\n🧹 Arquivo temporário removido")

    print("\n" + "="*60)
    print("Teste concluído!")
    print("="*60 + "\n")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        mode = sys.argv[1].lower()
    else:
        print("\n" + "="*60)
        print("DOCUMENT SEARCH TOOL - DocSeeker v6 Improved")
        print("="*60)
        print("\nEscolha o modo de execução:")
        print("1. GUI - Interface Gráfica (Tkinter)")
        print("2. Web - Interface Web (Flask)")
        print("3. Test - Testar OCR")
        print("4. Exit - Sair")

        choice = input("\nDigite sua escolha [1/2/3/4]: ").strip()

        if choice == '1':
            mode = 'gui'
        elif choice == '2':
            mode = 'web'
        elif choice == '3':
            mode = 'test'
        else:
            print("Saindo...")
            sys.exit(0)

    if mode == "web":
        print("\n🌐 Iniciando interface Web...")
        print("Acesse: http://localhost:5000")
        app.run(debug=True, use_reloader=False)
    elif mode == "test":
        # Modo de teste OCR
        test_path = input(
            "\nDigite o caminho de uma imagem para testar (ou ENTER para usar imagem de teste): ").strip()
        if test_path and os.path.exists(test_path):
            test_ocr_functionality(test_path)
        else:
            test_ocr_functionality()
    else:
        print("\n🖥️ Iniciando interface GUI...")
        run_interface()
