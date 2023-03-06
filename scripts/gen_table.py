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

def get_remaining(row):
   gen, extr, test, total = float(row['gen_cand']), float(row['proof-reduction']), float(row['pruning']), float(row['runtime'])
   return total - (gen + extr + test)

schema = [
   ('Example', lambda row : row['name'] ),
   # ('Data Structures', lambda row: data[row['name']][0]),
   # ('Refactoring', lambda row: data[row['name']][3]),
   # ('For/While', lambda row: to_check(data[row['name']][1])),
   # ('HOF', lambda row: to_check(data[row['name']][2])),
   ('Heap', lambda row: format_int(row['heap-candidates'])),
   ('Pure', lambda row: format_int(row['pure-candidates'])),
   ('Total', lambda row: format_int(get_total(row['heap-candidates'], row['pure-candidates']))),
   # ('# Admits (# Obligations)', lambda row: f"{row['no-admits'] or '0'} ({row['proof-obligations']})"),
   ('Generation', lambda row: format_float(row['gen_cand'])),
   ('Extraction', lambda row: format_float(row['proof-reduction'])),
   ('Testing', lambda row: format_float(row['pruning'])),
   ('Remaining', lambda row: format_float(get_remaining(row))),
   ('Total', lambda row: format_float(row['runtime'], no_precision=True))
]

order = {
   'seq_to_array': 1,
   'make_rev_list': 2,
   'tree_to_array': 3,
   'array_exists': 4,
   'array_find_mapi': 5,
   'array_is_sorted': 6,
   'array_findi': 7,
   'array_of_rev_list': 8,
   'array_foldi': 9,
   'array_partition': 10,
   'stack_filter': 11,
   'stack_reverse': 12,
   'sll_partition': 13,
   'sll_of_array': 14
}

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

    \\begin{{tabular}}[t]{{lcccccccccc}}
       \\toprule
       \\multirow{{Example}} & \\multicolumn{{3}}{{c}}{{Candidates}} &
                                                                    \\multicolumn{{4}}{{c}}{{Time (s)}} & \\multirow{{Total (s)}} \\\\
       \\cmidrule(lr){{2-4}} \\cmidrule(lr){{5-8}}
              & Heap & Pure & Total & Generation & Extraction & Testing & Remaining &  \\\\
      \\midrule
    """

    postlude = """
    \\bottomrule
    \\end{tabular}
    """

    print(prelude)

    stats.sort(key=lambda row: order[row['name']])
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
