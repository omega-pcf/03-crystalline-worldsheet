#!/usr/bin/env python3
"""
CW6_propgraph_dot.py — regenerate CW6_propgraph.dot and CW6_propgraph_stats.txt
from the CW6 alignment ledger JSON (cw6.lea/3.0).
"""
import json, os, collections

PROJECT = os.path.dirname(os.path.abspath(__file__))
JSON_IN = os.path.join(PROJECT, "CW6_alignment_ledger.json")
OUT_DOT = os.path.join(PROJECT, "CW6_propgraph.dot")
OUT_STAT = os.path.join(PROJECT, "CW6_propgraph_stats.txt")


def load_ledger():
    with open(JSON_IN, encoding="utf-8") as f:
        return json.load(f)


def build_graph(entries):
    """Build nodes and edges from ledger entries.
    Node = entry label. Edge = label references another label (via lean_decls or tex_tags)."""
    nodes = {}
    edges = collections.defaultdict(set)

    for e in entries:
        label = e["label"]
        nodes[label] = {
            "section": e.get("section", "?"),
            "equation": e.get("equation", ""),
            "lean_decls": e.get("lean_decls", []),
            "tex_tags": e.get("tex_tags", []),
            "numerical": e.get("numerical", ""),
        }

    # Build edges: for each entry's lean_decls, find other entries sharing those decls
    decl_to_labels = collections.defaultdict(set)
    for e in entries:
        for d in e.get("lean_decls", []):
            decl_to_labels[d].add(e["label"])

    # Entries sharing lean decls are connected
    for decl, labels in decl_to_labels.items():
        labels = sorted(labels)
        for i in range(len(labels)):
            for j in range(i + 1, len(labels)):
                edges[labels[i]].add(labels[j])
                edges[labels[j]].add(labels[i])

    return nodes, edges


def generate_dot(nodes, edges):
    """Generate DOT graph."""
    lines = [
        "digraph props {",
        "  rankdir=LR;",
        '  node [shape=box, fontsize=8, style=filled, fillcolor="#f8f8f0"];',
    ]
    for n in sorted(nodes, key=lambda x: nodes[x]["section"]):
        o = nodes[n]
        lean_count = len(o["lean_decls"])
        has_num = "N" if o["numerical"] else ""
        tag = f"P:{lean_count}" if lean_count else "—"
        if has_num:
            tag += f"/{has_num}"
        short = n.replace("eq:", "").replace("thm:", "").replace("prop:", "").replace("def:", "").replace("cor:", "").replace("rmk:", "")
        label = f"{short}\\n{tag}"
        lines.append(f'  "{n}" [label="{label}"];')
    for a in sorted(edges):
        for b in sorted(edges[a]):
            lines.append(f'  "{a}" -> "{b}";')
    lines.append("}")
    return "\n".join(lines)


def generate_stats(nodes, edges):
    """Generate stats text."""
    by_section = collections.Counter(o["section"][:1] for o in nodes.values())
    lean_count = sum(1 for o in nodes.values() if o["lean_decls"])
    num_count = sum(1 for o in nodes.values() if o["numerical"])
    both_count = sum(1 for o in nodes.values() if o["lean_decls"] and o["numerical"])
    neither = sum(1 for o in nodes.values() if not o["lean_decls"] and not o["numerical"])
    total_decls = sum(len(o["lean_decls"]) for o in nodes.values())
    ne = sum(len(v) for v in edges.values())
    iso = [n for n in nodes if not edges[n]]

    lines = [
        f"  entries: {len(nodes)}",
        f"  edges (shared lean decls): {ne}",
        f"  unique lean declarations referenced: {total_decls}",
        f"  with lean proof: {lean_count}",
        f"  with numerical check: {num_count}",
        f"  with both: {both_count}",
        f"  with neither: {neither}",
        f"  isolated (no edges): {len(iso)}",
        f"  by chapter: {dict(by_section)}",
        "",
    ]
    return "\n".join(lines)


def main():
    data = load_ledger()
    entries = data.get("entries", [])
    print(f"Loaded {len(entries)} entries from ledger")

    nodes, edges = build_graph(entries)
    print(f"Built graph: {len(nodes)} nodes, {sum(len(v) for v in edges.values())} edges")

    dot = generate_dot(nodes, edges)
    with open(OUT_DOT, "w", encoding="utf-8") as f:
        f.write(dot + "\n")
    print(f"Wrote {OUT_DOT}")

    stats = generate_stats(nodes, edges)
    with open(OUT_STAT, "w", encoding="utf-8") as f:
        f.write("\n" + stats + "\n")
    print(f"Wrote {OUT_STAT}")


if __name__ == "__main__":
    main()
