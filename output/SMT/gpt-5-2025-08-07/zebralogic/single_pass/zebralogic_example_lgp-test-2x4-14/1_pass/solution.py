import json
from z3 import Int, Solver, Distinct, And, sat

def solve_puzzle():
    houses = [1, 2]

    # Values in each category
    names = ["Eric", "Arnold"]
    styles = ["victorian", "colonial"]
    smoothies = ["cherry", "desert"]
    pets = ["dog", "cat"]

    # Position variables: pos_<category>_<value> = house index (1..2)
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_style = {s: Int(f"pos_style_{s}") for s in styles}
    pos_smoothie = {sm: Int(f"pos_smoothie_{sm}") for sm in smoothies}
    pos_pet = {p: Int(f"pos_pet_{p}") for p in pets}

    s = Solver()

    # Domain constraints: each position is in {1, 2}
    for var_group in (pos_name, pos_style, pos_smoothie, pos_pet):
        for v in var_group.values():
            s.add(And(v >= 1, v <= 2))
        # All-different within each category
        s.add(Distinct(list(var_group.values())))

    # Clues:
    # 1. The person who likes Cherry smoothies is the person who owns a dog.
    s.add(pos_smoothie["cherry"] == pos_pet["dog"])

    # 2. The person residing in a Victorian house is the person who owns a dog.
    s.add(pos_style["victorian"] == pos_pet["dog"])

    # 3. The person residing in a Victorian house is somewhere to the left of Eric.
    s.add(pos_style["victorian"] < pos_name["Eric"])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build rows per house
    rows = []
    for h in houses:
        # Find which value in each category sits at house h
        name_at_h = next(n for n in names if m[pos_name[n]].as_long() == h)
        style_at_h = next(st for st in styles if m[pos_style[st]].as_long() == h)
        smoothie_at_h = next(sm for sm in smoothies if m[pos_smoothie[sm]].as_long() == h)
        pet_at_h = next(p for p in pets if m[pos_pet[p]].as_long() == h)
        rows.append([str(h), name_at_h, style_at_h, smoothie_at_h, pet_at_h])

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
            "rows": rows
        }
    }

    print(json.dumps(output))

if __name__ == "__main__":
    solve_puzzle()