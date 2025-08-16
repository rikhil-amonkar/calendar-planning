import json
from z3 import Solver, Int, Distinct, And, Implies

def solve_puzzle():
    # Domains
    houses = [0, 1]  # internal 0-based; will output as 1-based strings
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]

    # Index helpers
    name_idx = {v: i for i, v in enumerate(names)}
    hair_idx = {v: i for i, v in enumerate(hair_colors)}
    sport_idx = {v: i for i, v in enumerate(sports)}
    smoothie_idx = {v: i for i, v in enumerate(smoothies)}

    # Variables: for each house, an int index into each domain
    Name = [Int(f"Name_{h}") for h in houses]
    Hair = [Int(f"Hair_{h}") for h in houses]
    Sport = [Int(f"Sport_{h}") for h in houses]
    Smoothie = [Int(f"Smoothie_{h}") for h in houses]

    s = Solver()

    # Domain constraints
    for h in houses:
        s.add(Name[h] >= 0, Name[h] < len(names))
        s.add(Hair[h] >= 0, Hair[h] < len(hair_colors))
        s.add(Sport[h] >= 0, Sport[h] < len(sports))
        s.add(Smoothie[h] >= 0, Smoothie[h] < len(smoothies))

    # Uniqueness across houses
    s.add(Distinct(*Name))
    s.add(Distinct(*Hair))
    s.add(Distinct(*Sport))
    s.add(Distinct(*Smoothie))

    # Clue 1: The Desert smoothie lover is Arnold.
    for h in houses:
        s.add((Smoothie[h] == smoothie_idx["desert"]) == (Name[h] == name_idx["Arnold"]))

    # Clue 2: The person who has brown hair is the person who loves basketball.
    for h in houses:
        s.add((Hair[h] == hair_idx["brown"]) == (Sport[h] == sport_idx["basketball"]))

    # Clue 3: Arnold is somewhere to the left of the person who has black hair.
    for i in houses:
        for j in houses:
            s.add(Implies(And(Name[i] == name_idx["Arnold"], Hair[j] == hair_idx["black"]), i < j))

    assert s.check().r == 1, "No solution found"
    m = s.model()

    # Build output rows in house order 1..N
    rows = []
    for h in houses:
        rows.append([
            str(h + 1),
            names[m[Name[h]].as_long()],
            hair_colors[m[Hair[h]].as_long()],
            sports[m[Sport[h]].as_long()],
            smoothies[m[Smoothie[h]].as_long()],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": rows
        }
    }

    print(json.dumps(output))

if __name__ == "__main__":
    solve_puzzle()