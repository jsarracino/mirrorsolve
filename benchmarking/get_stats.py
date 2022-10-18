#!/usr/bin/env python

from dataclasses import dataclass

import re
import sys
import os

from typing import Any, Optional

@dataclass
class GoalTally:
  completed: int
  total: int

  def pretty(self):
    return f"{self.completed}/{self.total}"

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
    return f"{self.crush.pretty()}, {self.hammer.pretty()}, {self.mirror.pretty()}"

  @staticmethod
  def empty():
    return ProverTally(crush=GoalTally.empty(), hammer=GoalTally.empty(), mirror=GoalTally.empty())

  def __add__(self, rhs:Any):
    return ProverTally(
      crush=self.crush + rhs.crush, 
      hammer=self.hammer + rhs.hammer,
      mirror=self.mirror + rhs.mirror
    )



def make_header():
  return "File, Crush completed/total, Hammer completed/total, MirrorSolve completed/total"

def pretty_row(x: ProverTally):
  return x.pretty()

# gather up stats for crush/hammer/mirrorsolve and count solved/total at the goal level, i.e. 15/16 is 15 of 16 goals solved
def read_file_goals(f_name: str, keep_field: Optional[str] = None) -> ProverTally:
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

            if keep_field and not payload[keep_field]:
              continue

            total = payload["goals"]
            ms_res = GoalTally(completed=payload["ms"], total=total)
            crush_res = GoalTally(completed=payload["crush"], total=total)
            hammer_res = GoalTally(completed=payload["hammer"], total=total)

            stats += ProverTally(mirror=ms_res, crush=crush_res, hammer=hammer_res)

          except Exception as e:
            print(f"malformed payload at {lineno}: {val}")
            print(e)
  return stats

# gather up stats for crush/hammer/mirrorsolve and count solved/total at the lemma level, i.e. 15/16 is 15 of 16 lemmas completely solved
def read_file_lemmas(f_name: str, keep_field: Optional[str] = None) -> ProverTally:
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

            if keep_field and not payload[keep_field]:
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
  return stats

if __name__ == "__main__":

  files = sys.argv

  print("Goals, original:")

  print(make_header())

  for fl in sys.argv[1:]:
    stats = read_file_goals(fl, "original")
    print(f"{os.path.basename(fl)}, {pretty_row(stats)}")

print("Goals, total:")

print(make_header())

for fl in sys.argv[1:]:
  stats = read_file_goals(fl)
  print(f"{os.path.basename(fl)}, {pretty_row(stats)}")

print("Lemmas, original:")

print(make_header())

for fl in sys.argv[1:]:
  stats = read_file_lemmas(fl, "original")
  print(f"{os.path.basename(fl)}, {pretty_row(stats)}")

print("Lemmas, total:")

print(make_header())

for fl in sys.argv[1:]:
  stats = read_file_lemmas(fl)
  print(f"{os.path.basename(fl)}, {pretty_row(stats)}")
