from z3 import Solver, Int, Distinct, And, Or, Implies
import json

def solve_puzzle():
    # Domains
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]

    num_houses = 2

    # Variables per house (indexed 0..num_houses-1)
    name = [Int(f"name_{i}") for i in range(num_houses)]
    sport = [Int(f"sport_{i}") for i in range(num_houses)]
    hobby = [Int(f"hobby_{i}") for i in range(num_houses)]

    s = Solver()

    # Domain constraints
    for i in range(num_houses):
        s.add(And(name[i] >= 0, name[i] < len(names)))
        s.add(And(sport[i] >= 0, sport[i] < len(sports)))
        s.add(And(hobby[i] >= 0, hobby[i] < len(hobbies)))

    # Uniqueness across houses
    s.add(Distinct(name))
    s.add(Distinct(sport))
    s.add(Distinct(hobby))

    # Clue 1: The person who enjoys gardening is Arnold.
    idx_arnold = names.index("Arnold")
    idx_gardening = hobbies.index("gardening")
    for i in range(num_houses):
        s.add(Implies(hobby[i] == idx_gardening, name[i] == idx_arnold))
        s.add(Implies(name[i] == idx_arnold, hobby[i] == idx_gardening))

    # Clue 2: The photography enthusiast is not in the first house.
    idx_photography = hobbies.index("photography")
    s.add(hobby[0] != idx_photography)

    # Clue 3: The person who loves soccer is not in the first house.
    idx_soccer = sports.index("soccer")
    s.add(sport[0] != idx_soccer)

    if s.check() != 1:  # 1 == z3.sat
        raise RuntimeError("No solution found")

    m = s.model()

    rows = []
    for i in range(num_houses):
        row = [
            str(i + 1),
            names[m[name[i]].as_long()],
            sports[m[sport[i]].as_long()],
            hobbies[m[hobby[i]].as_long()],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()