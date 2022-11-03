#!/usr/bin/env python3

import csv
import argparse

def to_header(name):
   return ' '.join([x.capitalize() for x in name.split('-')])

def normalize(s):
    return s.replace('_', '\\_') if s else '-'

def to_row(headers, row):
    return ' & '.join([normalize(row[h]) for h in headers])

def gen_table(path):
    with open(path) as f:
        reader = csv.DictReader(f)
        stats = list(reader)
        headers = stats[0].keys()


    col_spec = '{' +  'l' + 'c' * (len(headers) -1) + '}'

    col_headers = ' & '.join(list(map(to_header, headers)))

    prelude = f"""
    \\begin{{center}}
     \\begin{{tabular}}[t]{col_spec}
       \\toprule
      {col_headers} \\\\
      \\midrule
    """

    postlude = """
    \\bottomrule
    \\end{tabular}
    \\end{center}
    """

    print(prelude)

    for stat in stats:
        print(f"{to_row(headers, stat)} \\\\")

    print(postlude)

parser = argparse.ArgumentParser(
    prog = 'gen_table.py',
    description = 'Generates a LaTeX table from Sisyphus stats (see: lib/configuration for details)')

parser.add_argument('filename')
if __name__ == '__main__':
    args = parser.parse_args()
    gen_table(args.filename)
