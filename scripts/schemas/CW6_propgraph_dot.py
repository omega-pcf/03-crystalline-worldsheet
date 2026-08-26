#!/usr/bin/env python3
"""
CW6_propgraph_dot.py — regenerate CW6_propgraph.dot and CW6_propgraph_stats.txt
using the new P/N/Hyp verification tags instead of the old tier system.

Parses all .tex files in src/chapters/ for label, ref, and verification tags.
"""
import sys, re, collections, glob, os

# ── configuration ──────────────────────────────────────────────────────────
PROJECT  = "/home/aficio/Documents/DevelopmentV2/03-crystalline-worldsheet"
CHAPTERS = sorted(glob.glob(os.path.join(PROJECT, "src/chapters/*.tex")))
OUT_DOT  = os.path.join(PROJECT, "scripts/schemas/CW6_propgraph.dot")
OUT_STAT = os.path.join(PROJECT, "scripts/schemas/CW6_propgraph_stats.txt")

THM_ENVS = ['definition', 'lemma', 'theorem', 'proposition', 'corollary', 'remark',
            'claim', 'conjecture', 'example', 'notation', 'convention', 'assumption']
OBJ_PREFIX = ('prop:', 'thm:', 'lem:', 'cor:', 'def:', 'rmk:', 'asm:', 'clm:', 'conj:')

# Verification tag maps
TAG_P   = 'P'   # Lean proof
TAG_N   = 'N'   # numerical check
TAG_HYP = 'Hyp' # hypothesis from literature
TAG_CONJ = 'Conj' # conjectured, not proven
TAG_OPEN = 'Open' # open question


def parse_chapters():
    """Parse all chapter tex files. Return (combined_tex, objs dict, owner dict, global_file_map)."""
    objs = {}       # label -> {env, file, line, title, tags, body}
    owner = {}      # eq:label -> enclosing obj label
    file_map = {}   # label -> file basename (for stats)
    
    for fpath in CHAPTERS:
        fname = os.path.basename(fpath)
        tex = open(fpath, encoding='utf-8').read()
        lines_before = 0  # track line offset within this file
        
        for env in THM_ENVS:
            i = 0
            while True:
                b = tex.find('\\begin{' + env + '}', i)
                if b < 0:
                    break
                d, k, e = 0, b, -1
                while k < len(tex):
                    nb = tex.find('\\begin{' + env + '}', k)
                    ne = tex.find('\\end{' + env + '}', k)
                    if ne < 0:
                        break
                    if 0 <= nb < ne:
                        d += 1
                        k = nb + 1
                    else:
                        d -= 1
                        k = ne + 1
                        if d == 0:
                            e = ne + len('\\end{' + env + '}')
                            break
                if e < 0:
                    break
                body = tex[b:e]
                # Include trailing proof (same logic as original script)
                tail = tex[e:e + 200]
                mp = re.match(r'\s*(?:\\begin\{proof\}|\\begin\{proof\}\[[^\]]*\])', tail)
                if mp:
                    pe = tex.find('\\end{proof}', e)
                    if pe > 0:
                        body += tex[e:pe + len('\\end{proof}')]
                lab = re.search(r'\\label\{([^}]*)\}', body)
                if lab and lab.group(1).startswith(OBJ_PREFIX):
                    name = lab.group(1)
                    ttl = re.search(r'\\begin\{' + env + r'\}\[(.*?)\]', body, re.S)
                    
                    # Extract verification tags
                    tags = extract_tags(body)
                    
                    objs[name] = dict(
                        env=env,
                        file=fname,
                        line=tex[:b].count('\n') + 1,
                        title=re.sub(r'\s+', ' ', ttl.group(1)) if ttl else None,
                        tags=tags,
                        body=body
                    )
                    file_map[name] = fname
                    for eq in re.findall(r'\\label\{(eq:[^}]*)\}', tex[b:e]):
                        owner[eq] = name
                i = e
    
    return objs, owner, file_map


def extract_tags(body):
    """Extract verification tags from a theorem environment body.
    Returns dict with keys: 'P', 'N', 'Hyp', 'Conj', 'Open'."""
    tags = {}
    
    # \P{ref1, ref2, ...}
    p_matches = re.findall(r'\\P\{([^}]*)\}', body)
    if p_matches:
        refs = []
        for m in p_matches:
            refs.extend([r.strip() for r in m.split(',') if r.strip()])
        tags['P'] = refs if refs else []
    
    # \N{ref1, ref2, ...}
    n_matches = re.findall(r'\\N\{([^}]*)\}', body)
    if n_matches:
        refs = []
        for m in n_matches:
            refs.extend([r.strip() for r in m.split(',') if r.strip()])
        tags['N'] = refs
    
    # \Hyp{ref}
    hyp_matches = re.findall(r'\\Hyp\{([^}]*)\}', body)
    if hyp_matches:
        refs = [r.strip() for r in hyp_matches if r.strip()]
        tags['Hyp'] = refs
    
    # \Conj (no arguments)
    if re.search(r'\\Conj\b', body):
        tags['Conj'] = True
    
    # \Open (no arguments)
    if re.search(r'\\Open\b', body):
        tags['Open'] = True
    
    return tags


def verify_tag_display(tags):
    """Return a compact tag string for node labels.
    Omits zero-count entries for cleaner display."""
    parts = []
    if 'P' in tags:
        p_count = len(tags['P'])
        if p_count:
            parts.append(f"P:{p_count}")
        else:
            parts.append("P")
    if 'N' in tags:
        n_count = len(tags['N'])
        if n_count:
            parts.append(f"N:{n_count}")
        else:
            parts.append("N")
    if 'Hyp' in tags:
        hyp_count = len(tags['Hyp'])
        if hyp_count:
            parts.append(f"H:{hyp_count}")
        else:
            parts.append("H")
    if tags.get('Conj'):
        parts.append("Conj")
    if tags.get('Open'):
        parts.append("Open")
    return '/'.join(parts) if parts else '—'


def build_edges(objs, owner):
    """Build directed edges: obj -> obj. \\ref{obj} or \\eqref{eq:y} -> owner of eq:y."""
    edges = collections.defaultdict(set)
    for name, o in objs.items():
        for m in re.finditer(r'\\(?:eq)?ref\*?\{([^}]*)\}', o['body']):
            t = m.group(1)
            tgt = t if t.startswith(OBJ_PREFIX) else owner.get(t)
            if tgt and tgt in objs and tgt != name:
                edges[name].add(tgt)
    rev = collections.defaultdict(set)
    for a, bs in edges.items():
        for b in bs:
            rev[b].add(a)
    return edges, rev


def generate_dot(objs, edges, order):
    """Generate DOT graph string."""
    lines = ['digraph props {', '  rankdir=LR; node [shape=box, fontsize=9];']
    for n in order:
        o = objs[n]
        tag_str = verify_tag_display(o['tags'])
        label = f"{n}\\n{o['env'][:4]}\\n{tag_str}"
        lines.append(f'  "{n}" [label="{label}"];')
    for a in order:
        for b in sorted(edges[a]):
            lines.append(f'  "{a}" -> "{b}";')
    lines.append('}')
    return '\n'.join(lines)


def generate_stats(objs, edges, rev, owner, file_map, order):
    """Generate stats text."""
    ne = sum(len(v) for v in edges.values())
    byenv = collections.Counter(o['env'] for o in objs.values())
    iso = [n for n in order if not edges[n] and not rev[n]]
    fw = sum(1 for a in order for b in edges[a] if order.index(b) > order.index(a))
    
    # Verification tag distribution
    tag_counts = {'P': 0, 'N': 0, 'Hyp': 0, 'Conj': 0, 'Open': 0}
    for o in objs.values():
        if 'P' in o['tags']: tag_counts['P'] += 1
        if 'N' in o['tags']: tag_counts['N'] += 1
        if 'Hyp' in o['tags']: tag_counts['Hyp'] += 1
        if o['tags'].get('Conj'): tag_counts['Conj'] += 1
        if o['tags'].get('Open'): tag_counts['Open'] += 1
    
    # Objects with no verification tag
    untagged = [n for n in order if not objs[n]['tags']]
    
    # File distribution
    byfile = collections.Counter(file_map.get(n, '?') for n in order)
    
    lines = [
        f"  nodos (objetos tipo-teorema): {len(objs)}",
        f"  aristas objeto->objeto:       {ne}",
        f"  ecuaciones con dueño:         {len(owner)}",
        f"  por tipo: {dict(byenv)}",
        f"  aislados: {len(iso)}   citas hacia adelante: {fw}   hacia atrás: {ne-fw}",
        "",
        "  Verification tag distribution:",
        f"    \\P{{}} (Lean proof):     {tag_counts['P']}",
        f"    \\N{{}} (numerical):      {tag_counts['N']}",
        f"    \\Hyp{{}} (hypothesis):   {tag_counts['Hyp']}",
        f"    \\Conj (conjectured):     {tag_counts['Conj']}",
        f"    \\Open (open):            {tag_counts['Open']}",
        f"    untagged:                 {len(untagged)}",
        "",
        "  File distribution:",
    ]
    for f, c in byfile.most_common():
        lines.append(f"    {f:45s} {c}")
    
    lines.append("")
    lines.append("  El contraste que motiva esta herramienta: {} ecuaciones se".format(len(owner)))
    lines.append("  reparten en {} objetos. Medir conexiones sobre las ecuaciones".format(len(objs)))
    lines.append("  cuenta como 'conectadas' las que solo comparten contenedor.\n")
    
    return '\n'.join(lines)


def main():
    print("Parsing chapter files...")
    objs, owner, file_map = parse_chapters()
    print(f"  Found {len(objs)} objects, {len(owner)} equations with owners")
    
    edges, rev = build_edges(objs, owner)
    order = sorted(objs, key=lambda n: objs[n]['line'])
    
    # Generate DOT
    dot = generate_dot(objs, edges, order)
    os.makedirs(os.path.dirname(OUT_DOT), exist_ok=True)
    with open(OUT_DOT, 'w', encoding='utf-8') as f:
        f.write(dot + '\n')
    print(f"  Wrote {OUT_DOT}")
    
    # Generate stats
    stats = generate_stats(objs, edges, rev, owner, file_map, order)
    with open(OUT_STAT, 'w', encoding='utf-8') as f:
        f.write('\n' + stats + '\n')
    print(f"  Wrote {OUT_STAT}")
    
    # Summary
    ne = sum(len(v) for v in edges.values())
    print(f"\n  Summary: {len(objs)} nodes, {ne} edges, {len(owner)} equations")
    tag_counts = collections.Counter()
    for o in objs.values():
        for k in o['tags']:
            tag_counts[k] += 1
    print(f"  Tags: {dict(tag_counts)}")


if __name__ == '__main__':
    main()
