#!/usr/bin/env python3

import argparse
import sys
import re

import logging
logging.basicConfig(
  format='%(asctime)s %(levelname)-8s %(message)s',
  level=logging.INFO,
  stream=sys.stdout,
  datefmt='%Y-%m-%d %H:%M:%S')


# convert lines of output into a list of file, typename, result
def process_file(fp: str) -> list[str]:
  ret : list[str] = []
  # 2022-10-04 22:08:09 INFO     extracted types for powerpc/Builtins1.v to: [('Builtins1.platform_builtin', True)]
  line_matcher = r".*extracted \w+ for (.+) to: \[(.*)\]"
  # ('FIX.beta', False), ('FIX.emin', False), ('FIX.FIX_format', None)
  with open(fp, 'r') as f:
    for line in f:
      if (match := re.match(line_matcher, line)):
        # split the list of tuples into each individual tuple
        tuples = match.group(2).split("),") if len(match.group(2)) else []
        # split each tuple into two different items
        tuples_split = [x.split(',') for x in tuples]
        # clean up parens and whitespace
        cleaned_tuples = [[x.strip().strip('(').strip(')').strip("'").replace("None", "-").replace("True", "1").replace("False","0") for x in tuple] for tuple in tuples_split]

        for tup in cleaned_tuples:
          ret.append(match.group(1) + "," + tup[0] + "," + tup[1])
  
  return ret

def main():
    # Parse the command line arguments.
  parser = argparse.ArgumentParser(description="convert the output of eval into a csv")
  parser.add_argument('-i', '--input', required=True, help="input path")
  args = parser.parse_args()

  ret = process_file(args.input)
  for line in ret:
    print(line)

if __name__ == "__main__":
  main()