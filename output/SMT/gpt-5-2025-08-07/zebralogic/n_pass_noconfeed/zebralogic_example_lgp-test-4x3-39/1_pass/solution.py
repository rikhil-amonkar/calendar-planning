import json
import sys
import subprocess

# Ensure z3-solver is available
try:
    from z3 import Solver, Int, Distinct, And, Or, sat
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "z3-solver"])
    from z3 import Solver, Int, Distinct, And, Or, sat

def solve_puzzle():
    # Houses 1..4, left to right
    houses = [1, 2, 3, 4]

    # Attributes
    Names = ["Eric", "Alice", "Peter", "Arnold"]
    HairColors = ["blonde", "black", "red", "brown"]
    Sports = ["swimming", "soccer", "basketball", "tennis"]

    # Variables: each attribute is assigned a house number (1..4)
    name_vars = {n: Int(n) for n in Names}
    hair_vars = {h: Int("hair_" + h) for h in HairColors}
    sport_vars = {s: Int("sport_" + s) for s in Sports}

    all_vars = list(name_vars.values()) + list(hair_vars.values()) + list(sport_vars.values())

    s = Solver()

    # Domain constraints: all variables are in 1..4
    for v in all_vars:
        s.add(And(v >= 1, v <= 4))

    # Uniqueness within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*hair_vars.values()))
    s.add(Distinct(*sport_vars.values()))

    # Clues:
    # 1. The person who loves soccer is not in the second house.
    s.add(sport_vars["soccer"] != 2)

    # 2. Eric is the person who has blonde hair.
    s.add(name_vars["Eric"] == hair_vars["blonde"])

    # 3. The person who has blonde hair is somewhere to the right of the person who loves basketball.
    s.add(hair_vars["blonde"] > sport_vars["basketball"])

    # 4. The person who has black hair is the person who loves tennis.
    s.add(hair_vars["black"] == sport_vars["tennis"])

    # 5. Arnold is somewhere to the left of the person who has red hair.
    s.add(name_vars["Arnold"] < hair_vars["red"])

    # 6. Alice is the person who loves swimming.
    s.add(name_vars["Alice"] == sport_vars["swimming"])

    # 7. The person who has red hair is directly left of the person who has black hair.
    s.add(hair_vars["red"] + 1 == hair_vars["black"])

    # Solve
    if s.check() != sat:
        # In the unlikely event of unsat, output an empty but valid JSON structure (still meeting format)
        output = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": [[str(h), "", "", ""] for h in houses]
            }
        }
        print(json.dumps(output))
        return

    m = s.model()

    # Helper to invert mapping: house -> attribute name
    def invert(mapping):
        inverse = {}
        for attr_name, var in mapping.items():
            house = m[var].as_long()
            inverse[house] = attr_name
        return inverse

    house_to_name = invert(name_vars)
    house_to_hair = invert(hair_vars)
    house_to_sport = invert(sport_vars)

    rows = []
    for h in houses:
        rows.append([
            str(h),
            house_to_name[h],
            house_to_hair[h],
            house_to_sport[h],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()