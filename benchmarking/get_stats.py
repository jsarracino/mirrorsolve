#!/usr/bin/env python

from dataclasses import dataclass

import re
import sys
import os

from typing import Any, Optional, Callable, Tuple

@dataclass
class GoalTally:
  completed: int
  total: int

  def pretty(self):
    percentage = "{0:.0%}".format(float(self.completed)/float(self.total) if self.total else 1.0)
    return f"{self.completed} ({percentage})"

  @staticmethod
  def empty():
    return GoalTally(completed=0, total=0)

  def __add__(self, rhs:Any):
    return GoalTally(completed=self.completed + rhs.completed, total=self.total + rhs.total)


@dataclass
class ProverTally:
  crush: GoalTally
  hammer: GoalTally
  mirror: GoalTally

  def pretty(self):
    return f"{self.crush.total}, {self.crush.pretty()}, {self.hammer.pretty()}, {self.mirror.pretty()}"

  @staticmethod
  def empty():
    return ProverTally(crush=GoalTally.empty(), hammer=GoalTally.empty(), mirror=GoalTally.empty())

  def __add__(self, rhs:Any):
    return ProverTally(
      crush=self.crush + rhs.crush, 
      hammer=self.hammer + rhs.hammer,
      mirror=self.mirror + rhs.mirror
    )
  
  @staticmethod
  def make_header():
    return "Total, Crush, Hammer, MirrorSolve"


@dataclass
class ExpressivenessTally:
  total: int
  sfo: int
  tsfo: int
  ho: int

  def pretty(self):
    return f"{self.total}, {self.sfo}, {self.tsfo}, {self.ho}"

  @staticmethod
  def empty():
    return ExpressivenessTally(total=0, sfo=0, tsfo=0, ho=0)

  def __add__(self, rhs:Any):
    return ExpressivenessTally(
      total=self.total + rhs.total, 
      sfo=self.sfo + rhs.sfo, 
      tsfo=self.tsfo + rhs.tsfo, 
      ho=self.ho + rhs.ho, 
    )

  @staticmethod
  def make_header():
    return "Total Goals, Locally FO, Transitively FO, HO"

@dataclass
class EffortTally:
  lemmas: int
  definitions: int
  edits: int

  def pretty(self):
    return f"{self.lemmas}, {self.definitions}, {self.edits}"

  @staticmethod
  def empty():
    return EffortTally(lemmas=0, definitions=0, edits=0)

  def __add__(self, rhs:Any):
    return EffortTally(
      lemmas=self.lemmas + rhs.lemmas, 
      definitions=self.definitions + rhs.definitions, 
      edits=self.edits + rhs.edits, 
    )

  @staticmethod
  def make_header():
    return "Reflection Lemmas, Extra Definitions, Modified Lemmas"



# gather up stats for crush/hammer/mirrorsolve and count solved/total at the goal level, i.e. 15/16 is 15 of 16 goals solved
def read_file_goals(f_name: str, keep_field: Optional[Tuple[str, Callable[[Any], bool]]] = None) -> ProverTally:
  stats = ProverTally.empty()
  with open(f_name) as f:
    for lineno, line in enumerate(f, start=1):
      line = line.strip()
      ms_prefix_re = r"\(\*\*\* MS"
      ms_prefix_match = re.match(ms_prefix_re, line)

      if not ms_prefix_match:
        continue

      rest = line[ms_prefix_match.end():].split()
      match rest[0]:
        case "LEMMA":
          val = ' '.join(rest[1:-1])
          try:
            payload = eval(val)

            if keep_field and not keep_field[1](payload[keep_field[0]]):
              continue

            total = payload["goals"]
            ms_res = GoalTally(completed=payload["ms"], total=total)
            crush_res = GoalTally(completed=payload["crush"], total=total)
            hammer_res = GoalTally(completed=payload["hammer"], total=total)

            stats += ProverTally(mirror=ms_res, crush=crush_res, hammer=hammer_res)

          except Exception as e:
            print(f"malformed payload at {lineno}: {val}")
            print(e)

        case _:
          continue
  return stats

# gather up stats for crush/hammer/mirrorsolve and count solved/total at the lemma level, i.e. 15/16 is 15 of 16 lemmas completely solved
def read_file_lemmas(f_name: str, keep_field: Optional[Tuple[str, Callable[[Any], bool]]] = None) -> ProverTally:
  stats = ProverTally.empty()
  with open(f_name) as f:
    for lineno, line in enumerate(f, start=1):
      line = line.strip()
      ms_prefix_re = r"\(\*\*\* MS"
      ms_prefix_match = re.match(ms_prefix_re, line)

      if not ms_prefix_match:
        continue

      rest = line[ms_prefix_match.end():].split()
      match rest[0]:
        case "LEMMA":
          val = ' '.join(rest[1:-1])
          try:
            payload = eval(val)

            if keep_field and not keep_field[1](payload[keep_field[0]]):
              continue

            total = payload["goals"]
            ms_completed = 1 if payload["ms"] == total else 0
            crush_completed = 1 if payload["crush"] == total else 0
            hammer_completed = 1 if payload["hammer"] == total else 0

            ms_res = GoalTally(completed=ms_completed, total=1)
            crush_res = GoalTally(completed=crush_completed, total=1)
            hammer_res = GoalTally(completed=hammer_completed, total=1)



            stats += ProverTally(mirror=ms_res, crush=crush_res, hammer=hammer_res)

          except Exception as e:
            print(f"malformed payload at {lineno}: {val}")
            print(e)

        case _:
          continue
  return stats

def read_file_expressiveness(f_name: str) -> ExpressivenessTally:
  stats = ExpressivenessTally.empty()
  with open(f_name) as f:
    for lineno, line in enumerate(f, start=1):
      line = line.strip()
      ms_prefix_re = r"\(\*\*\* MS"
      ms_prefix_match = re.match(ms_prefix_re, line)

      if not ms_prefix_match:
        continue

      rest = line[ms_prefix_match.end():].split()
      match rest[0]:
        case "LEMMA":
          val = ' '.join(rest[1:-1])
          try:
            payload = eval(val)

            if not payload["original"]:
              continue
            
            stats += ExpressivenessTally(
              total=1,
              sfo=1 if payload["sfo"] else 0,
              tsfo=1 if payload["tsfo"] else 0,
              ho=1 if payload["ho"] else 0,
            )

          except Exception as e:
            print(f"malformed payload at {lineno}: {val}")
            print(e)
        case "EXTRA":
          val = ' '.join(rest[1:-1])
          try:
            payload = eval(val)

            stats += ExpressivenessTally(
              total=payload["count"],
              sfo=0,
              tsfo=0,
              ho=payload["count"],
            )

          except Exception as e:
            print(f"malformed payload at {lineno}: {val}")
            print(e)
          continue
        case _:
          continue
  return stats

def read_file_effort(f_name: str) -> EffortTally:
  stats = EffortTally.empty()
  with open(f_name) as f:
    for lineno, line in enumerate(f, start=1):
      line = line.strip()
      ms_prefix_re = r"\(\*\*\* MS"
      ms_prefix_match = re.match(ms_prefix_re, line)

      if not ms_prefix_match:
        continue

      rest = line[ms_prefix_match.end():].split()
      match rest[0]:
        case "EFFORT":
          val = ' '.join(rest[1:-1])
          try:
            payload = eval(val)

            match payload["type"]:
              case "definition":
                rhs = EffortTally(lemmas=0,definitions=1,edits=0)
              case "lemma":
                rhs = EffortTally(lemmas=1,definitions=0,edits=0)
              case "edit":
                rhs = EffortTally(lemmas=0,definitions=0,edits=1)
              case _:
                raise Exception(f"Unrecognized effort payload {payload}")
            
            stats += rhs

          except Exception as e:
            print(f"malformed payload at {lineno}: {val}")
            print(e)
  
        case _:
          continue
  return stats

if __name__ == "__main__":

  files = sys.argv[1:]

  print("Expressiveness table:")
  print("\\toprule")
  print(('Bench, ' + ExpressivenessTally.make_header()).replace(',',' &') + " \\\\")
  print("\\midrule")
  

  aggregate = ExpressivenessTally.empty()
  
  for fl in files:
    stats = read_file_expressiveness(fl)
    aggregate += stats
    print(f"{os.path.basename(fl).split('.')[0]}, {stats.pretty()} \\\\".replace(',',' &'))

  print("\\midrule")
  print(f"Total, {aggregate.pretty()} \\\\".replace(',',' &'))
  print("\\bottomrule")
  

  print("goal table:")
  print("\\toprule")
  print(('Bench, ' + ProverTally.make_header()).replace(',',' &') + " \\\\")
  print("\\midrule")
  

  helper_aggregate = ProverTally.empty()
  original_aggregate = ProverTally.empty()

  
  for i, fl in enumerate(files):
    helper_stats = read_file_goals(fl, ("original", lambda x: not x))
    original_stats = read_file_goals(fl, ("original", lambda x: x))
    total_stats = helper_stats + original_stats
    print(f"{os.path.basename(fl).split('.')[0]} (helper), {helper_stats.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
    print(f"{os.path.basename(fl).split('.')[0]} (original), {original_stats.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
    print(f"{os.path.basename(fl).split('.')[0]} (total), {total_stats.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))

    if i < len(files) + 1:
      print("\\cmidrule{2-5}")

    helper_aggregate += helper_stats
    original_aggregate += original_stats

  print("\\midrule")
  print(f"Aggregate (helper), {helper_aggregate.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
  print(f"Aggregate (original), {original_aggregate.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
  print(f"Aggregate (total), {(helper_aggregate + original_aggregate).pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
  print("\\bottomrule")


  print("lemma table:")
  print("\\toprule")
  print(('Bench, ' + ProverTally.make_header()).replace(',',' &') + " \\\\")
  print("\\midrule")

  helper_aggregate = ProverTally.empty()
  original_aggregate = ProverTally.empty()

  
  for i, fl in enumerate(files):
    helper_stats = read_file_lemmas(fl, ("original", lambda x: not x))
    original_stats = read_file_lemmas(fl, ("original", lambda x: x))
    total_stats = helper_stats + original_stats
    print(f"{os.path.basename(fl).split('.')[0]} (helper), {helper_stats.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
    print(f"{os.path.basename(fl).split('.')[0]} (original), {original_stats.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
    print(f"{os.path.basename(fl).split('.')[0]} (total), {total_stats.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))

    if i < len(files) + 1:
      print("\\cmidrule{2-5}")

    helper_aggregate += helper_stats
    original_aggregate += original_stats

  print("\\midrule")
  print(f"Aggregate (helper), {helper_aggregate.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
  print(f"Aggregate (original), {original_aggregate.pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
  print(f"Aggregate (total), {(helper_aggregate + original_aggregate).pretty()} \\\\".replace(',',' &').replace('%', '\\%'))
  print("\\bottomrule")

  print("Effort table:")
  print("\\toprule")
  print(('Bench, ' + EffortTally.make_header()).replace(',',' &') + " \\\\")
  print("\\midrule")

  aggregate = EffortTally.empty()
  
  for fl in files:
    stats = read_file_effort(fl)
    aggregate += stats
    print(f"{os.path.basename(fl).split('.')[0]}, {stats.pretty()} \\\\".replace(',',' &'))

  print("\\midrule")
  print(f"Total, {aggregate.pretty()} \\\\".replace(',',' &'))
  print("\\bottomrule")
  

  