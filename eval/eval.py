#!/usr/bin/env python3

import os, sys
import shutil

sys.path.append(os.path.dirname(os.path.realpath(__file__)))

from dataclasses import dataclass
from typing import ParamSpec, TypeVar, final, Generic, Any

import argparse
import multiprocessing
import functools
import sys
import contextlib
import json
import re

from sexpdata import Symbol, parse

import coq_serapy as serapi_instance

from coq_serapy import kill_comments

# from coq_serapy_scraper.util import eprint, mybarfmt

from typing import List, Tuple, Optional

import logging
logging.basicConfig(
  format='%(asctime)s %(levelname)-8s %(message)s',
  level=logging.INFO,
  stream=sys.stdout,
  datefmt='%Y-%m-%d %H:%M:%S')

from os import chdir, getcwd

_stack = []

def pushd(dir):
    global _stack
    _stack.append(getcwd())
    chdir(dir)

def popd():
    chdir(_stack.pop())

match_redirect = r"-R ([a-zA-Z0-9_\-.]+) ([a-zA-Z0-9_\-.]+)"

def replace_redirects(s: str, prefix: str):
  def replacer(m: re.Match):
    return f"-R {prefix + '/' + m.group(1)},{m.group(2)}"
  return re.sub(match_redirect, replacer, s)


def main():
    # Parse the command line arguments.
  parser = argparse.ArgumentParser(description="scrape a proof")
  parser.add_argument('-j', '--threads', default=1, type=int)
  parser.add_argument('-c', '--continue', dest='cont', default=False, const=True, action='store_const')
  parser.add_argument('--hardfail', default=False, const=True, action='store_const')
  parser.add_argument('--type', default=False, const=True, action='store_const')
  parser.add_argument('--prelude', default=".")
  parser.add_argument('-v', '--verbose', action='count', default=0)
  parser.add_argument("--progress", "-P", help="show progress of files", action='store_const', const=True, default=False)
  parser.add_argument('--skip-nochange-tac', default=False, const=True,
                      action='store_const',
                      dest='skip_nochange_tac')
  parser.add_argument('inputs', nargs="+", help="proof file name(s) (*.v)")
  args = parser.parse_args()
  includes = None
  try:
    with open(args.prelude + "/_CoqProject", 'r') as includesfile:
      # includes = includesfile.read()
      pass
  except FileNotFoundError:
    logging.error("Didn't find a _CoqProject file in prelude dir", args.prelude)
  # Set up the command which runs sertop.
  coqargs = ["sertop", "--implicit"]
  # if includes:
  #   logging.info("extra coqargs:")
  #   logging.info(replace_redirects(includes, args.prelude))
  #   coqargs += replace_redirects(includes, args.prelude).splitlines()

  if args.type:
    iter_file = iter_file_type
  else:
    iter_file = iter_file_prop

  if args.threads > 1:
    tasks = [(idx % args.threads, filename) for (idx, filename) in enumerate(args.inputs)]
    with multiprocessing.Pool(args.threads) as pool:
      result_files = pool.imap(
        functools.partial(iter_file, coqargs, args),
        tasks
      )
      for idx, result_file in enumerate(result_files, start=1):
        if result_file is None:
          logging.warning(f"Failed file {idx} of {len(args.inputs)}")
        else:
          if args.verbose:
            logging.info(f"Finished file {idx} of {len(args.inputs)}")
  else:
    for idx, fn in enumerate(args.inputs, start=1):
      res = iter_file(coqargs, args, (1,fn))
      match res:
        case Inl(res):
          if args.type:
            logging.info(f"extracted types for {fn} to: {res}")
          else:
            logging.info(f"extracted props for {fn} to: {res}")
        case Inr(fname):
          logging.error(f"failed on file: {fname}")

type_starting_patterns = [
    # r"Variables?",
    # r"Definition",
    r"Inductive",
    r"Record"]


def possibly_starting_type(command: str) -> Optional[re.Match[str]]:
    stripped_command = kill_comments(command).strip()
    pattern = r"(.*)(" + "|".join(type_starting_patterns) + r")(.*)"
    program_pat = r".*Program.*"
    if not re.match(program_pat, stripped_command):
      return re.match(pattern, stripped_command)
    else:
      return None

A = TypeVar('A')
B = TypeVar('B')

class Sum(Generic[A, B]):
  x: A | B

@dataclass(frozen=True)
@final
class Inl(Generic[A, B], Sum[A, B]):
  x: A

@dataclass(frozen=True)
@final
class Inr(Generic[A, B], Sum[A, B]):
  x: B


def make_fo_type_test (x: str):
  return f"""
MetaCoq Run (
  MetaCoq.Template.TemplateMonad.Core.tmBind (MetaCoq.Template.TemplateMonad.Core.tmQuoteRec {x}) (fun x => 
  MetaCoq.Template.TemplateMonad.Core.tmBind (MirrorSolve.Eval.is_fo_type x) (fun x => 
  MetaCoq.Template.TemplateMonad.Core.tmBind (MetaCoq.Template.TemplateMonad.Core.tmEval MetaCoq.Template.TemplateMonad.Common.all x) (fun x => 
  MetaCoq.Template.TemplateMonad.Core.tmPrint x
))))."""

def make_fo_prop_test (x: str):
  return f"""
MetaCoq Run (
  MetaCoq.Template.TemplateMonad.Core.tmBind (MirrorSolve.Eval.is_fo_const {x})  (fun x => 
  MetaCoq.Template.TemplateMonad.Core.tmBind (MetaCoq.Template.TemplateMonad.Core.tmEval MetaCoq.Template.TemplateMonad.Common.all x) (fun x => 
  MetaCoq.Template.TemplateMonad.Core.tmPrint x
)))."""

def add_prelude(coq: serapi_instance.SerapiInstance):
  coq.run_stmt("From MetaCoq.Template Require All Loader.")
  coq.run_stmt("Require MirrorSolve.Eval.")
  coq.run_stmt("Local Unset Asymmetric Patterns.")
  coq.run_stmt("Local Set Auto Template Polymorphism.")
  coq.run_stmt("Local Obligation Tactic := Tactics.program_simpl.")
  coq.run_stmt("Arguments eq_refl {A}%type_scope {x}, [_] _.")

# [Symbol('Feedback'), 
#   [
#     [Symbol('doc_id'), 0], 
#     [Symbol('span_id'), 23], 
#     [Symbol('route'), 0], 
#     [Symbol('contents'), 
#       [Symbol('Message'), 
#         [Symbol('level'), Symbol('Info')], 
#         [Symbol('loc'), []], 
#         [Symbol('pp'), [Symbol('Pp_box'), [Symbol('Pp_hovbox'), 1], [Symbol('Pp_glue'), [[Symbol('Pp_string'), '('], [Symbol('Pp_box'), [Symbol('Pp_hovbox'), 2], [Symbol('Pp_glue'), [[Symbol('Pp_tag'), Symbol('constr.variable'), [Symbol('Pp_string'), Symbol('Some')]], [Symbol('Pp_print_break'), 1, 0], [Symbol('Pp_tag'), Symbol('constr.variable'), [Symbol('Pp_string'), Symbol('true')]]]]], [Symbol('Pp_string'), ')']]]]], 
#         [Symbol('str'), '(Some true)']]]]]

def parse_response(resp: Any):
  interior = resp[1][3][-1][-1]

  assert isinstance(interior[0], Symbol) and interior[0].value() == 'str'

  if isinstance(interior[1], Symbol):
    if interior[1].value() == "None":
      return None
    else:
      assert False

  val = parse(interior[1])

  if isinstance(val, list):
    assert len(val) == 1
    val = val[0]
    if len(val) == 2:
      if val[-1].value() == 'true':
        return True
      elif val[-1].value() == 'false':
        return False
      else:
        assert False
    else:
      assert False
  else:
    assert False

def check_fo(coq: serapi_instance.SerapiInstance, x: str, type_test: bool = False):
  coq.run_stmt(make_fo_type_test(x) if type_test else make_fo_prop_test(x))

  _, _, the_response, _ = coq.feedbacks

  try:
    ret = parse_response(the_response)
    return Inl(ret)
  except:
    logging.error("couldn't parse response:")
    logging.error(the_response)
    return Inr(None)

def get_defn_ident(defn: re.Match[str]) -> Optional[str]:
  try:
    orig = defn[0]
    pref_end = defn.end(2)
    ident = orig[pref_end:-1].split()[0]
    if ident[-1] == ":":
      return ident[:-1]
    else:
      return ident
  except:
    return None


def iter_file_type(coqargs: List[str], args: argparse.Namespace, file_tuple: Tuple[int, str]) -> Sum[List[Tuple[str, Any]], str]:
  sys.setrecursionlimit(4500)
  file_idx, filename = file_tuple
  pushd(args.prelude)
  full_filename = filename
  commands = serapi_instance.load_commands_preserve(args, file_idx, str(full_filename))

  try:
    with \
      serapi_instance.SerapiContext(
          coqargs
        , serapi_instance.get_module_from_filename(filename)
        , '.'
        , False) as coq:

      coq.verbose = args.verbose
      ret : List[Tuple[str, Any]] = []
      

      add_prelude(coq)

      # coq.check_term("eq_refl 0")
      # logging.info(coq.coq_minor_version())

      for cmd in commands: 
        coq.run_stmt(cmd)
        if (mtch := possibly_starting_type(cmd)):
          if (ident := get_defn_ident(mtch)):
            # logging.info(f"checking type of {mtch.groups()}")
            match check_fo(coq, ident, type_test=True):
              case Inl(r):
                ret.append((coq.module_prefix + ident, r))
              case Inr(_):
                logging.error(f"error parsing {ident}")
                logging.error("original command:")
                logging.error(cmd)

      return Inl(ret)
  except:
    return Inr(full_filename)
  finally:
    popd()

thm_match = r".*(Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property)\s+([a-zA-Z_](\w|')+)\s*(.*)" 

def replace_first_semi(thm_rhs: str) -> str:
  in_paren = 0
  
  for i, c in enumerate(thm_rhs):
    if c == '(':
      in_paren += 1
    elif c == ')':
      in_paren -= 1
    elif c == ':' and not in_paren:
      return thm_rhs[0:i] + ':=' + thm_rhs[i+1:]
  
  assert False

def iter_file_prop(coqargs: List[str], args: argparse.Namespace, file_tuple: Tuple[int, str]) -> Sum[List[Tuple[str, Any]], str]:
  sys.setrecursionlimit(4500)
  file_idx, filename = file_tuple
  pushd(args.prelude)
  full_filename = filename
  commands = serapi_instance.load_commands_preserve(args, file_idx, str(full_filename))

  try:
    with \
      serapi_instance.SerapiContext(
          coqargs
        , serapi_instance.get_module_from_filename(filename)
        , '.'
        , False) as coq:

      coq.verbose = args.verbose
      ret : List[Tuple[str, Any]] = []

      add_prelude(coq)

      counter = 0

      for cmd in commands: 
        # logging.info(cmd)
        if (mtch := re.match(thm_match, cmd.replace('\n', ' ').strip())):
          # logging.info("prop to check:")
          # logging.info(mtch.group(4))
          name = f"ms__prop__{counter}"
          add_cmd = f"Definition {name} {replace_first_semi(mtch.group(4))}"
          coq.run_stmt(add_cmd)
          # logging.info(f"added: {add_cmd}")

          match check_fo(coq, name, type_test=False):
            case Inl(r):
              ret.append((coq.module_prefix + mtch.group(2), r))
            case Inr(_):
              logging.error(f"error parsing prop for {mtch.group(2)}")
              logging.error("original command:")
              logging.error(cmd)
          counter += 1
        else:
          if serapi_instance.possibly_starting_proof(cmd):
            # logging.warn("skipping possible proof:")
            # logging.warn(cmd)
            pass
        

        coq.run_stmt(cmd)

      return Inl(ret)
  except:
    return Inr(full_filename)
  finally:
    popd()

test = """
Lemma nlist_forall2_imply:
  forall (A B: Type) (P1: A -> B -> Prop) (l1: nlist A) (l2: nlist B),
  nlist_forall2 P1 l1 l2 ->
  forall (P2: A -> B -> Prop),
  (forall v1 v2, nIn v1 l1 -> nIn v2 l2 -> P1 v1 v2 -> P2 v1 v2) ->
  nlist_forall2 P2 l1 l2.
"""
if __name__ == "__main__":
  main()
