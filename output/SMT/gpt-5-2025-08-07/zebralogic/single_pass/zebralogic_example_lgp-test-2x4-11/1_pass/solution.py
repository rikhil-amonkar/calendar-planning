from z3 import Solver, Int, Distinct, Or, sat
import json

def safe_name(s):
    return s.replace(" ", "_")

def solve():
    houses = [1, 2]

    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    pets = ["cat", "dog"]
    heights = ["short", "very short"]

    s = Solver()

    Name = {n: Int(f"Name_{safe_name(n)}") for n in names}
    Hobby = {h: Int(f"Hobby_{safe_name(h)}") for h in hobbies}
    Pet = {p: Int(f"Pet_{safe_name(p)}") for p in pets}
    Height = {h: Int(f"Height_{safe_name(h)}") for h in heights}

    # Domain constraints
    for group in (Name, Hobby, Pet, Height):
        for v in group.values():
            s.add(Or([v == h for h in houses]))

    # Uniqueness within each category
    s.add(Distinct([Name[n] for n in names]))
    s.add(Distinct([Hobby[h] for h in hobbies]))
    s.add(Distinct([Pet[p] for p in pets]))
    s.add(Distinct([Height[h] for h in heights]))

    # Clues:
    # 1. The person who is very short is the photography enthusiast.
    s.add(Height["very short"] == Hobby["photography"])
    # 2. Eric is the person who is very short.
    s.add(Name["Eric"] == Height["very short"])
    # 3. The person who has a cat is somewhere to the right of the person who is very short.
    s.add(Pet["cat"] > Height["very short"])

    assert s.check() == sat
    m = s.model()

    # Build rows in house order
    rows = []
    for h in houses:
        name_val = next(k for k, v in Name.items() if m[v].as_long() == h)
        hobby_val = next(k for k, v in Hobby.items() if m[v].as_long() == h)
        pet_val = next(k for k, v in Pet.items() if m[v].as_long() == h)
        height_val = next(k for k, v in Height.items() if m[v].as_long() == h)
        rows.append([str(h), name_val, hobby_val, pet_val, height_val])

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Pet", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    solve()