import json
from z3 import Int, Solver, And, Or, Distinct

def solve_puzzle():
    # Enumerations
    NAMES = ["Eric", "Peter", "Arnold"]
    MOTHERS = ["Holly", "Aniya", "Janelle"]
    FOODS = ["pizza", "grilled cheese", "spaghetti"]

    N_idx = {name: i for i, name in enumerate(NAMES)}
    M_idx = {mother: i for i, mother in enumerate(MOTHERS)}
    F_idx = {food: i for i, food in enumerate(FOODS)}

    # Variables for each house (0-based index for houses 1..3)
    name = [Int(f"name_{i}") for i in range(3)]
    mother = [Int(f"mother_{i}") for i in range(3)]
    food = [Int(f"food_{i}") for i in range(3)]

    s = Solver()

    # Domain constraints
    for i in range(3):
        s.add(name[i] >= 0, name[i] < 3)
        s.add(mother[i] >= 0, mother[i] < 3)
        s.add(food[i] >= 0, food[i] < 3)

    # Uniqueness constraints
    s.add(Distinct(*name))
    s.add(Distinct(*mother))
    s.add(Distinct(*food))

    # Clue 3: The person who loves eating grilled cheese is Eric.
    for i in range(3):
        s.add((name[i] == N_idx["Eric"]) == (food[i] == F_idx["grilled cheese"]))

    # Clue 2: The person who loves eating grilled cheese is directly left of
    #         The person whose mother's name is Aniya.
    s.add(Or(
        And(food[0] == F_idx["grilled cheese"], mother[1] == M_idx["Aniya"]),
        And(food[1] == F_idx["grilled cheese"], mother[2] == M_idx["Aniya"])
    ))

    # Clue 4: Peter is The person whose mother's name is Holly.
    for i in range(3):
        s.add((name[i] == N_idx["Peter"]) == (mother[i] == M_idx["Holly"]))

    # Clue 1 (interpreted): The spaghetti eater and Peter are next to each other.
    s.add(Or(
        And(food[0] == F_idx["spaghetti"], name[1] == N_idx["Peter"]),
        And(name[0] == N_idx["Peter"], food[1] == F_idx["spaghetti"]),
        And(food[1] == F_idx["spaghetti"], name[2] == N_idx["Peter"]),
        And(name[1] == N_idx["Peter"], food[2] == F_idx["spaghetti"])
    ))

    assert s.check().r == 1, "Puzzle is unsatisfiable"
    m = s.model()

    # Build result
    rows = []
    for i in range(3):
        n = NAMES[m[name[i]].as_long()]
        mo = MOTHERS[m[mother[i]].as_long()]
        f = FOODS[m[food[i]].as_long()]
        rows.append([str(i + 1), n, mo, f])

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    res = solve_puzzle()
    print(json.dumps(res, ensure_ascii=False, indent=2))