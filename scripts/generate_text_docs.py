import os
from pathlib import Path
import re

SOURCE_DIR = Path("../Mlc")
DOCS_DIR = Path("../docs")
DOCS_DIR.mkdir(exist_ok=True)

FILES = [
    "Yoccoz",
    "Quadratic/Complex/Groetzsch", "Quadratic/Complex/Basic", "Quadratic/Complex/Green",
    "Quadratic/Complex/GreenLemmas", "Quadratic/Complex/Puzzle", "Quadratic/Complex/PuzzleLemmas",
    "Quadratic/Complex/Escape"
]

def sanitize_tex(text):
    chars = {
        '\\': r'\textbackslash{}',
        '{': r'\{',
        '}': r'\}',
        '$': r'\$',
        '&': r'\&',
        '#': r'\#',
        '^': r'\textasciicircum{}',
        '_': r'\_',
        '%': r'\%',
        '~': r'\textasciitilde{}'
    }

    # 1. Handle Headers: # Title -> \textbf{Title}
    lines = text.split('\n')
    processed_lines = []
    
    for line in lines:
        match = re.match(r'^(#+)\s+(.*)', line)
        if match:
            # It's a header. Escape the content, wrap in bold.
            content = match.group(2)
            safe_content = ""
            for c in content:
                if c in chars: safe_content += chars[c]
                else: safe_content += c
            processed_lines.append(f"\\textbf{{{safe_content}}}")
        else:
            # Normal line. Escape it.
            safe_line = ""
            for c in line:
                if c in chars: safe_line += chars[c]
                else: safe_line += c
            processed_lines.append(safe_line)
            
    text = '\n'.join(processed_lines)
    
    # 2. Handle List items
    text = re.sub(r'(?m)^\s*-\s+', r'\\textbullet\\ ', text)
    
    # 2b. Handle code blocks `code` -> \texttt{code}
    # Naive replacement: odd ` is start, even ` is end.
    # We use a regex.
    text = re.sub(r'`([^`]+)`', r'\\texttt{\1}', text)

    # 3. Replace Unicode with Math
    replacements = {
        'ℂ': r'$\mathbb{C}$',
        'ℝ': r'$\mathbb{R}$',
        'ℕ': r'$\mathbb{N}$',
        'ℤ': r'$\mathbb{Z}$',
        '∀': r'$\forall$',
        '∃': r'$\exists$',
        '∈': r'$\in$',
        '∉': r'$\notin$',
        '⊆': r'$\subseteq$',
        '⊂': r'$\subset$',
        '∩': r'$\cap$',
        '∪': r'$\cup$',
        '⋂': r'$\bigcap$',
        '⋃': r'$\bigcup$',
        '≤': r'$\le$',
        '≥': r'$\ge$',
        '→': r'$\to$',
        '↔': r'$\leftrightarrow$',
        '↦': r'$\mapsto$',
        '₀': r'$_0$',
        '₁': r'$_1$',
        '²': r'$^2$',
        '⁻¹': r'$^{-1}$',
        'ψ': r'$\psi$',
        'φ': r'$\varphi$',
        'λ': r'$\lambda$',
        'ε': r'$\varepsilon$',
        'δ': r'$\delta$',
        '∂': r'$\partial$',
        '∆': r'$\Delta$',
        '∅': r'$\emptyset$',
        '⟨': r'$\langle$',
        '⟩': r'$\rangle$',
    }
    
    for char, rep in replacements.items():
        text = text.replace(char, rep)
        
    return text

def generate_stub(lean_file):
    base_name = Path(lean_file).stem
    tex_path = DOCS_DIR / f"{base_name}.tex"
    
    with open(SOURCE_DIR / f"{lean_file}.lean", "r") as f:
        content = f.read()
    
    # Simple docstring extraction: find module docstring /-! ... -/
    module_doc = ""
    match = re.search(r"/-\!(.*?)-/", content, re.DOTALL)
    if match:
        module_doc = match.group(1).strip()
    
    # Create tex content
    tex_content = f"\\section{{{base_name.replace('_', '\\_')}}}\n"
    tex_content += f"\\textit{{Source: \\texttt{{{lean_file.replace('_', '\\_')}.lean}}}}\n\n"
    
    if module_doc:
        tex_content += "\\begin{quotation}\n"
        tex_content += sanitize_tex(module_doc) + "\n"
        tex_content += "\\end{quotation}\n\n"
    else:
        tex_content += "This module contains the formal definitions and proofs.\n"

    # Simple regex to find theorems and their docstrings
    # Matches: /-- doc -/ theorem/lemma name ... :=
    pattern_lean4 = re.compile(r'/--(.*?)-/\s*(?:theorem|lemma|def|class|structure|instance)\s+(\w+)', re.DOTALL)
    
    for match in pattern_lean4.finditer(content):
        doc = match.group(1).strip()
        name = match.group(2)
        tex_content += f"\\subsection*{{{name.replace('_', '\\_')}}}\\label{{{name}}}\n"
        tex_content += f"{sanitize_tex(doc)}\n\n"
        tex_content += f"\\textit{{(See code: {name.replace('_', '\\_')})}}\n\n"

        
    with open(tex_path, "w") as f:
        f.write(tex_content)
    print(f"Generated {tex_path}")

if __name__ == "__main__":
    for f in FILES:
        generate_stub(f)
