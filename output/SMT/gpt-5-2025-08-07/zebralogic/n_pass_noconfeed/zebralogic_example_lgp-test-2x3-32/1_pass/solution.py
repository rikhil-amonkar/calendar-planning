import json
from z3 import Solver, Int, Distinct, And, Or, sat

def main():
    # Houses numbered from left (1) to right (2)
    houses = [1, 2]

    # Attributes
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]

    # Z3 variables: position (house index) of each attribute value
    name_pos = {n: Int(f"pos_name_{n}") for n in names}
    bday_pos = {b: Int(f"pos_bday_{b}") for b in birthdays}
    color_pos = {c: Int(f"pos_color_{c}") for c in colors}

    s = Solver()

    # Domain constraints: each position is in houses
    for d in (name_pos, bday_pos, color_pos):
        for v in d.values():
            s.add(Or([v == h for h in houses]))

    # Uniqueness constraints within each category
    s.add(Distinct([name_pos[n] for n in names]))
    s.add(Distinct([bday_pos[b] for b in birthdays]))
    s.add(Distinct([color_pos[c] for c in colors]))

    # Clues:
    # 1. Eric is the person who loves yellow.
    s.add(name_pos["Eric"] == color_pos["yellow"])

    # 2. The person whose birthday is in April is in the first house.
    s.add(bday_pos["april"] == 1)

    # 3. The person who loves yellow is not in the first house.
    s.add(color_pos["yellow"] != 1)

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Invert mappings: house -> attribute value
    def invert(pos_dict):
        inv = {h: None for h in houses}
        for val, var in pos_dict.items():
            inv[m[var].as_long()] = val
        return inv

    house_to_name = invert(name_pos)
    house_to_bday = invert(bday_pos)
    house_to_color = invert(color_pos)

    # Build output rows in house order
    rows = []
    for h in houses:
        rows.append([
            str(h),
            house_to_name[h],
            house_to_bday[h],
            house_to_color[h],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    main()