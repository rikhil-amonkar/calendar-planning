import json
from z3 import Int, Solver, Distinct, And

def solve_puzzle():
    houses = [1, 2]  # house indices from left (1) to right (2)

    # Attribute values
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    pets = ["cat", "dog"]
    heights = ["short", "very short"]

    # Create Z3 integer variables for the position (house number) of each attribute value
    name_vars = {n: Int(f"pos_name_{n}") for n in names}
    hobby_vars = {h: Int(f"pos_hobby_{h}") for h in hobbies}
    pet_vars = {p: Int(f"pos_pet_{p}") for p in pets}
    height_vars = {h: Int(f"pos_height_{h}") for h in heights}

    s = Solver()

    # Domain constraints: all positions are in [1, 2]
    for var in list(name_vars.values()) + list(hobby_vars.values()) + list(pet_vars.values()) + list(height_vars.values()):
        s.add(And(var >= houses[0], var <= houses[-1]))

    # Uniqueness constraints: each category assigns unique houses to its values
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*hobby_vars.values()))
    s.add(Distinct(*pet_vars.values()))
    s.add(Distinct(*height_vars.values()))

    # Clues:
    # 1. The person who is very short is the photography enthusiast.
    s.add(height_vars["very short"] == hobby_vars["photography"])

    # 2. Eric is the person who is very short.
    s.add(name_vars["Eric"] == height_vars["very short"])

    # 3. The person who has a cat is somewhere to the right of the person who is very short.
    s.add(pet_vars["cat"] > height_vars["very short"])

    # Solve
    if s.check() != 1:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Extract positions
    pos_names = {k: m.evaluate(v).as_long() for k, v in name_vars.items()}
    pos_hobbies = {k: m.evaluate(v).as_long() for k, v in hobby_vars.items()}
    pos_pets = {k: m.evaluate(v).as_long() for k, v in pet_vars.items()}
    pos_heights = {k: m.evaluate(v).as_long() for k, v in height_vars.items()}

    # Build rows in house order
    rows = []
    for h in houses:
        # Find the value for each category at house h
        name_at_h = next(n for n, p in pos_names.items() if p == h)
        hobby_at_h = next(n for n, p in pos_hobbies.items() if p == h)
        pet_at_h = next(n for n, p in pos_pets.items() if p == h)
        height_at_h = next(n for n, p in pos_heights.items() if p == h)

        rows.append([str(h), name_at_h, hobby_at_h, pet_at_h, height_at_h])

    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Pet", "Height"],
            "rows": rows
        }
    }

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))