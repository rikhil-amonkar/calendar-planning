import json
from z3 import Solver, Int, Distinct, And, Or, sat

def solve_puzzle():
    # Define houses
    houses = [1, 2]

    # Define attributes
    Names = ["Eric", "Arnold"]
    HouseStyles = ["victorian", "colonial"]
    Smoothies = ["cherry", "desert"]
    Pets = ["dog", "cat"]

    # Create Z3 variables: position (house index) of each attribute value
    name_pos = {n: Int(f"pos_name_{n}") for n in Names}
    style_pos = {s: Int(f"pos_style_{s}") for s in HouseStyles}
    smoothie_pos = {s: Int(f"pos_smoothie_{s}") for s in Smoothies}
    pet_pos = {p: Int(f"pos_pet_{p}") for p in Pets}

    s = Solver()

    # Domain constraints: each attribute value is placed in one of the houses
    for d in (name_pos, style_pos, smoothie_pos, pet_pos):
        for v in d.values():
            s.add(Or([v == h for h in houses]))

    # All-different constraints within each category
    s.add(Distinct([name_pos[n] for n in Names]))
    s.add(Distinct([style_pos[h] for h in HouseStyles]))
    s.add(Distinct([smoothie_pos[smo] for smo in Smoothies]))
    s.add(Distinct([pet_pos[p] for p in Pets]))

    # Clues:
    # 1. The person who likes Cherry smoothies is the person who owns a dog.
    s.add(smoothie_pos["cherry"] == pet_pos["dog"])

    # 2. The person residing in a Victorian house is the person who owns a dog.
    s.add(style_pos["victorian"] == pet_pos["dog"])

    # 3. The person residing in a Victorian house is somewhere to the left of Eric.
    s.add(style_pos["victorian"] < name_pos["Eric"])

    # Solve
    if s.check() != sat:
        raise Exception("Puzzle is unsatisfiable")

    m = s.model()

    # Inverse mapping: for each house, find which value of each attribute is there
    def invert(mapping):
        inv = {}
        for key, var in mapping.items():
            inv[m[var].as_long()] = key
        return inv

    name_at = invert(name_pos)
    style_at = invert(style_pos)
    smoothie_at = invert(smoothie_pos)
    pet_at = invert(pet_pos)

    # Build solution rows in house order
    rows = []
    for h in houses:
        rows.append([
            str(h),
            name_at[h],
            style_at[h],
            smoothie_at[h],
            pet_at[h],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": rows
        }
    }

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))