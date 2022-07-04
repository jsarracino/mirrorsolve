#!/usr/bin/env python

from dataclasses import dataclass

import re
import sys

from enum import Enum


@dataclass
class HammerStats:
  proof_size: int
  total: int
  finished: int

  def empty(): return HammerStats(0, 0, 0)

  def merge(self, r):
    return HammerStats(
        proof_size=self.proof_size + r.proof_size
      , total=self.total + r.total
      , finished=self.finished + r.finished
    )

  def heading():
    return f"Hammer Proof, Hammer Total, Hammer Success"
  def pretty(self):
    return f"{self.proof_size}, {self.total}, {self.finished}"

@dataclass 
class ProofStats:
  defn_size : int
  manual_size: int
  hammer: HammerStats
  ms_size: int
  ms_success: int
  
  def empty(): return ProofStats(0, 0, HammerStats.empty(), 0, 0)

  def merge(self, r):
    return ProofStats(
        defn_size=self.defn_size + r.defn_size
      , manual_size=self.manual_size + r.manual_size
      , hammer=self.hammer.merge(r.hammer)
      , ms_size=self.ms_size + r.ms_size
    )
  def heading():
    return f"Proof Definition, Manual Proof, {HammerStats.heading()}, MirrorSolve Proof, MirrorSolve Success"
  def pretty(self):
    return f"{self.defn_size}, {self.manual_size}, {self.hammer.pretty()}, {self.ms_size}, {self.ms_success}"

@dataclass
class BoilerStats:
  fol_defn: int
  uf_axioms: int
  quoting: int
  plugin: int

  def merge(self, r):
    return BoilerStats(
        fol_defn=self.fol_defn + r.fol_defn
      , uf_axioms=self.uf_axioms + r.uf_axioms
      , plugin=self.plugin + r.plugin
      , quoting=self.quoting + r.quoting
    )
  # def heading():
  #   return f"Implementation, {ProofStats.heading()}, {ConfigStats.heading()}"
  # def pretty(self):
  #   return f"{self.impl_size}, {self.proof.pretty()}, {self.config.pretty()}"

@dataclass
class ConfigStats:
  plugin_size: int
  tactics_size: int
  # boilerplate: BoilerStats
  boilerplate : int

  def empty(): return ConfigStats(0, 0, 0)

  def merge(self, r):
    return ConfigStats(
        plugin_size=self.plugin_size + r.plugin_size
      , tactics_size=self.tactics_size + r.tactics_size
      # , boilerplate=self.boilerplate.merge(r.plugin)
      , boilerplate=self.boilerplate + r.boilerplate
    )

  def heading():
    return f"Plugins, Tactics, Boilerplate"
  def pretty(self):
    return f"{self.plugin_size}, {self.tactics_size}, {self.boilerplate}"

@dataclass
class BenchStats:
  impl_size : int
  proof: ProofStats
  config: ConfigStats

  def empty(): return BenchStats(0, ProofStats.empty(), ConfigStats.empty())

  def merge(self, r):
    return BenchStats(
        impl_size=self.impl_size + r.impl_size
      , proof=self.proof.merge(r.proof)
      , config=self.config.merge(r.config)
    )

  def heading():
    return f"Implementation, {ProofStats.heading()}, {ConfigStats.heading()}"
  def pretty(self):
    return f"{self.impl_size}, {self.proof.pretty()}, {self.config.pretty()}"

def read_file(f_name: str, stats: BenchStats):
  with open(f_name) as f:
    counter = 0
    lineno = 0
    reading = False
    old_payload = None
    for line in f:
      lineno += 1
      line = line.strip()
      ms_prefix_re = r"\(\*\*\* MS"
      ms_prefix_match = re.match(ms_prefix_re, line)
      if ms_prefix_match:
        rest = line[ms_prefix_match.end():].split()
        match rest[0]:
          case "BEGIN":
            if reading:
              print(f"double open at {lineno}, exiting early")
              return stats
            else:
              reading = True
              val = ' '.join(rest[1:-1])
              payload = eval(val)
              assert "type" in payload, f"missing type in payload at {lineno}"
              match payload["type"]:
                case "configuration":
                  assert "config_type" in payload, f"missing config_type in payload at {lineno}"
                  match payload["config_type"]:
                    case "boilerplate" | "plugin" | "tactics":
                      old_payload = payload
                    case _ : 
                      print(f"""unrecogized reading state {payload["config_type"]} at {lineno}""")
                      reading = False
                case "proof":
                  assert "proof_type" in payload, f"missing proof_type in payload at {lineno}"
                  match payload["proof_type"]:
                    case "manual" | "hammer" | "mirrorsolve":
                      old_payload = payload
                    case _ : 
                      print(f"""unrecogized reading state {payload["proof_type"]} at {lineno}""")
                      reading = False
                case "proof_definition" | "definition":
                  old_payload = payload
                case _:
                  print(f"""unhandled payload type {payload["type"]} at {lineno}""")
                  reading = False       
          case "END":
            if not reading:
              print(f"unmatched close at {lineno}, exiting early")
              return stats
            else:
              old_counter = counter
              counter = 0
              reading = False
              val = ' '.join(rest[1:-1])
              payload = eval(val)
              assert old_payload == payload, f"inconsistent payloads at {lineno}: {old_payload} vs {payload}"
              assert "type" in payload, f"missing type in payload at {lineno}"
              match old_payload["type"]:
                case "configuration":
                  match old_payload["config_type"]:
                    case "boilerplate":
                      stats.config.boilerplate += old_counter
                    case "plugin":
                      stats.config.plugin_size += old_counter
                    case "tactics":
                      stats.config.tactics_size += old_counter
                    case _:
                      assert False, f"""unmatched payload {old_payload["config_type"]}"""
                case "proof":
                  match old_payload["proof_type"]:
                    case "manual":
                      stats.proof.manual_size += old_counter
                    case "hammer":
                      stats.proof.hammer.proof_size += old_counter
                      stats.proof.hammer.total += int(old_payload["total"])
                      stats.proof.hammer.finished += int(old_payload["finished"])
                    case "mirrorsolve":
                      stats.proof.ms_size += old_counter
                      assert "total" in old_payload, f"missing total in ms payload at {lineno}"
                      stats.proof.ms_success += old_payload["total"]
                    case _:
                      assert False
                case "proof_definition":
                  stats.proof.defn_size += old_counter
                case "definition":
                  stats.impl_size += old_counter
                case _:
                  print(f"""unhandled payload type {payload["type"]} at {lineno}""")
          case "STOP":
            print(f"stopping early at {lineno}")
            return stats
          case _:
            assert False, f"unhandled tag {rest[0]} at {lineno}"
      else:
        if reading: counter += 1
  return stats


if __name__ == "__main__":

  files = sys.argv

  stats = BenchStats.empty()

  for fl in sys.argv[1:]:
    print(f"reading stats from {fl}:")
    stats = read_file(fl, stats)

  print("overall stats:")
  print(BenchStats.heading())
  print(stats.pretty())