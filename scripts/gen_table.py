#!/usr/bin/env python3
import csv
import argparse
from os import statvfs_result

def get_total(num_heap, num_pure):
   num_heap = int(num_heap) if num_heap != '' else 1
   num_pure = int(num_pure) if num_pure != '' else 1
   return str(num_heap * num_pure)

# Delta DS, Delta Order Iteration, Delta Mutable/Pure
data = {
   # [data_structure, has_loop, has_hof]
   'seq_to_array': ['Array, Seq', False, False, 'Order of Iteration, Intermediate DS'],
   'sll_partition': ['SLL', True, True, 'Mutable to Pure, Order of Iteration'],
   'stack_filter': ['Stack', False, True, 'Intermediate DS'],
   'array_exists': ['Array', False, True, 'Mutable to Pure'],
   'stack_reverse': ['Stack', False, False, 'Intermediate DS'],
   'array_find_mapi': ['Array, Ref', True, True, 'Pure to Mutable'],
   'array_is_sorted': ['Array', True, True, 'Pure to Mutable'],
   'array_findi': ['Array', True, True, 'Pure to Mutable'],
   'sll_of_array': ['Array, SLL', False, False, 'Order of Iteration'],
   'array_foldi': ['Array', True, True, 'Pure to Mutable'],
   'array_partition': ['Array', True, True, 'Intermediate DS'],
   'tree_to_array': ['Array, Tree', False, False, 'Order of Iteration, Intermediate DS'],
   'make_rev_list': ['Ref', False, False, 'Mutable to Pure'],
   'array_of_rev_list': ['Array', True, False, 'Intermediate DS']
}

def to_check(b):
   return '$\\checkmark$' if b else ''

def format_int(vl):
   if vl:
      vl = int(vl)
      if vl >= 1000:
         vl_str = "{:.1e}".format(vl).replace('e+0', ' \\times 10^{')
         vl_str = vl_str.replace('e+', ' \\times 10^{')
         vl_str += "}"
         return f"${vl_str}$"
      else:
         return str(vl)
   else:
      return ''

def format_float(vl, no_precision=False):
   vl_f = float(vl)
   if vl_f < 0.005:
      return '$\\leq 5 \\textit{ms}$'
   else:
      return "{:.2f}".format(vl_f) if not no_precision else "{:.0f}".format(vl_f)

schema = [
   ('Example', lambda row : row['name'] ),
   ('Data Structures', lambda row: data[row['name']][0]),
   ('Refactoring', lambda row: data[row['name']][3]),
   ('For/While', lambda row: to_check(data[row['name']][1])),
   ('HOF', lambda row: to_check(data[row['name']][2])),
   ('Heap', lambda row: format_int(row['heap-candidates'])),
   ('Pure', lambda row: format_int(row['pure-candidates'])),
   ('Total', lambda row: format_int(get_total(row['heap-candidates'], row['pure-candidates']))),
   ('# Admits (# Obligations)', lambda row: f"{row['no-admits'] or '0'} ({row['proof-obligations']})"),
   ('Synthesis', lambda row: format_float(row['gen_cand'])),
   ('Reduction', lambda row: format_float(row['proof-reduction'])),
   ('Pruning', lambda row: format_float(row['pruning'])),
   ('Solver', lambda row: format_float(row['solver-time'])),
   ('Total', lambda row: format_float(row['runtime'], no_precision=True))
]

def normalize(s):
    return s.replace('_', '\\_') if s else '-'

def to_row(row):
   tex_row = [ normalize(col[1](row)) for col in schema]
   return ' & '.join(tex_row)

def gen_table(path):
    with open(path) as f:
        reader = csv.DictReader(f)
        stats = list(reader)
        headers = [col[0] for col in schema]


    col_spec = '{' +  'l' + 'c' * (len(headers) -1) + '}'

    col_headers = ' & '.join(headers)

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

    for row in stats:
        print(f"{to_row(row)} \\\\")

    print(postlude)

parser = argparse.ArgumentParser(
    prog = 'gen_table.py',
    description = 'Generates a LaTeX table from Sisyphus stats (see: lib/configuration for details)')

parser.add_argument('filename')
if __name__ == '__main__':
    args = parser.parse_args()
    gen_table(args.filename)
