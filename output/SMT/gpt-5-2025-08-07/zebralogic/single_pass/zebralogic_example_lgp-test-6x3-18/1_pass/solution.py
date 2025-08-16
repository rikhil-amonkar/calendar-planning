import json
from z3 import Int, Distinct, Solver, And, Or, Abs

def solve_puzzle():
    houses = range(1, 7)

    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    # Create Z3 variables: position (1..6) of each attribute value
    name_pos = {n: Int(f"name_{n}") for n in names}
    mother_pos = {m: Int(f"mother_{m}") for m in mothers}
    pet_pos = {p: Int(f"pet_{p}") for p in pets}

    s = Solver()

    # Domain constraints: each attribute must be in 1..6
    for d in (name_pos, mother_pos, pet_pos):
        for v in d.values():
            s.add(And(v >= 1, v <= 6))

    # All different within each category
    s.add(Distinct(*name_pos.values()))
    s.add(Distinct(*mother_pos.values()))
    s.add(Distinct(*pet_pos.values()))

    # Clues encoding

    # 1. Bob is not in the second house.
    s.add(name_pos["Bob"] != 2)

    # 2. Two houses between cat and rabbit: distance 3
    s.add(Abs(pet_pos["cat"] - pet_pos["rabbit"]) == 3)

    # 3. Cat is directly left of Holly
    s.add(pet_pos["cat"] + 1 == mother_pos["Holly"])

    # 4. Hamster is directly left of rabbit
    s.add(pet_pos["hamster"] + 1 == pet_pos["rabbit"])

    # 5. Rabbit is Eric
    s.add(name_pos["Eric"] == pet_pos["rabbit"])

    # 6. One house between dog and cat: distance 2
    s.add(Abs(pet_pos["dog"] - pet_pos["cat"]) == 2)

    # 7. Cat is Janelle (same person)
    s.add(pet_pos["cat"] == mother_pos["Janelle"])

    # 8. Alice is directly left of Carol
    s.add(name_pos["Alice"] + 1 == name_pos["Carol"])

    # 9. Carol's mother is Aniya
    s.add(name_pos["Carol"] == mother_pos["Aniya"])

    # 10. Arnold has a cat
    s.add(name_pos["Arnold"] == pet_pos["cat"])

    # 11. Kailyn is the rabbit's mother
    s.add(mother_pos["Kailyn"] == pet_pos["rabbit"])

    # 12. Fish owner has mother Sarah
    s.add(mother_pos["Sarah"] == pet_pos["fish"])

    if s.check() != 1:  # sat == 1
        raise RuntimeError("No solution found")

    m = s.model()

    # Invert position mappings to get attribute at each house
    pos_to_name = {m.evaluate(pos).as_long(): name for name, pos in name_pos.items()}
    pos_to_mother = {m.evaluate(pos).as_long(): mother for mother, pos in mother_pos.items()}
    pos_to_pet = {m.evaluate(pos).as_long(): pet for pet, pos in pet_pos.items()}

    rows = []
    for h in houses:
        rows.append([
            str(h),
            pos_to_name[h],
            pos_to_mother[h],
            pos_to_pet[h]
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()