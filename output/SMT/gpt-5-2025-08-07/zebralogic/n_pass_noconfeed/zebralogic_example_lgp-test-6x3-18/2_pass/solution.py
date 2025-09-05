import json
from z3 import Solver, Int, Distinct, Or, And, sat

def solve_puzzle():
    houses = list(range(1, 7))

    # Attributes
    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    # Position variables for each attribute (house numbers 1..6)
    name_pos = {n: Int(f"name_pos_{n}") for n in names}
    mother_pos = {m: Int(f"mother_pos_{m}") for m in mothers}
    pet_pos = {p: Int(f"pet_pos_{p}") for p in pets}

    s = Solver()

    # Domain constraints
    for var in list(name_pos.values()) + list(mother_pos.values()) + list(pet_pos.values()):
        s.add(var >= 1, var <= 6)

    # Uniqueness constraints (each attribute appears exactly once across houses)
    s.add(Distinct([name_pos[n] for n in names]))
    s.add(Distinct([mother_pos[m] for m in mothers]))
    s.add(Distinct([pet_pos[p] for p in pets]))

    # Clues:
    # 1. Bob is not in the second house.
    s.add(name_pos["Bob"] != 2)

    # 2. Two houses between cat and rabbit (distance 3).
    s.add(Or(pet_pos["cat"] + 3 == pet_pos["rabbit"],
             pet_pos["rabbit"] + 3 == pet_pos["cat"]))

    # 3. Cat is directly left of Holly.
    s.add(pet_pos["cat"] + 1 == mother_pos["Holly"])

    # 4. Hamster directly left of rabbit.
    s.add(pet_pos["hamster"] + 1 == pet_pos["rabbit"])

    # 5. Rabbit owner is Eric.
    s.add(name_pos["Eric"] == pet_pos["rabbit"])

    # 6. One house between dog and cat (distance 2).
    s.add(Or(pet_pos["dog"] + 2 == pet_pos["cat"],
             pet_pos["cat"] + 2 == pet_pos["dog"]))

    # 7. Cat owner has mother Janelle.
    s.add(pet_pos["cat"] == mother_pos["Janelle"])

    # 8. Alice is directly left of Carol.
    s.add(name_pos["Alice"] + 1 == name_pos["Carol"])

    # 9. Carol's mother is Aniya.
    s.add(name_pos["Carol"] == mother_pos["Aniya"])

    # 10. Arnold has a cat.
    s.add(name_pos["Arnold"] == pet_pos["cat"])

    # 11. Rabbit owner's mother is Kailyn.
    s.add(mother_pos["Kailyn"] == pet_pos["rabbit"])

    # 12. Fish owner has mother Sarah.
    s.add(pet_pos["fish"] == mother_pos["Sarah"])

    res = s.check()
    if res != sat:
        raise RuntimeError(f"No solution found (status: {res})")

    m = s.model()

    # Build result rows ordered by house number
    rows = []
    for h in houses:
        name_at_h = next(n for n in names if m.evaluate(name_pos[n]).as_long() == h)
        mother_at_h = next(mm for mm in mothers if m.evaluate(mother_pos[mm]).as_long() == h)
        pet_at_h = next(p for p in pets if m.evaluate(pet_pos[p]).as_long() == h)
        rows.append([str(h), name_at_h, mother_at_h, pet_at_h])

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))