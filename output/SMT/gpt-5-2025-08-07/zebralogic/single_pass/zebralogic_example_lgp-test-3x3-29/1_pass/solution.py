# pip install z3-solver
from z3 import Solver, Int, Distinct, And, Or, sat
import json

def solve():
    houses = [0, 1, 2]  # internal 0-based indexing for houses 1..3

    # Domains
    Names = ["Eric", "Peter", "Arnold"]
    Mothers = ["Holly", "Aniya", "Janelle"]
    Foods = ["pizza", "grilled cheese", "spaghetti"]

    def idx(lst, val):
        return lst.index(val)

    # Variables: for each house, assign index into Names/Mothers/Foods
    name = [Int(f"name_{h}") for h in houses]
    mother = [Int(f"mother_{h}") for h in houses]
    food = [Int(f"food_{h}") for h in houses]

    s = Solver()

    # Domain constraints: each variable in 0..2
    for h in houses:
        s.add(And(name[h] >= 0, name[h] < 3))
        s.add(And(mother[h] >= 0, mother[h] < 3))
        s.add(And(food[h] >= 0, food[h] < 3))

    # Uniqueness across houses
    s.add(Distinct(*name))
    s.add(Distinct(*mother))
    s.add(Distinct(*food))

    # Clue 3: The person who loves eating grilled cheese is Eric.
    # i.e., the grilled cheese eater has Name == Eric (same house)
    s.add(Or(
        And(food[0] == idx(Foods, "grilled cheese"), name[0] == idx(Names, "Eric")),
        And(food[1] == idx(Foods, "grilled cheese"), name[1] == idx(Names, "Eric")),
        And(food[2] == idx(Foods, "grilled cheese"), name[2] == idx(Names, "Eric")),
    ))

    # Clue 4: Peter is The person whose mother's name is Holly.
    # i.e., in the same house: Name == Peter and Mother == Holly
    s.add(Or(
        And(name[0] == idx(Names, "Peter"), mother[0] == idx(Mothers, "Holly")),
        And(name[1] == idx(Names, "Peter"), mother[1] == idx(Mothers, "Holly")),
        And(name[2] == idx(Names, "Peter"), mother[2] == idx(Mothers, "Holly")),
    ))

    # Clue 2: The person who loves eating grilled cheese is directly left of
    # The person whose mother's name is Aniya.
    # Left means house h is immediately before h+1 (0-based)
    s.add(Or(
        And(food[0] == idx(Foods, "grilled cheese"), mother[1] == idx(Mothers, "Aniya")),
        And(food[1] == idx(Foods, "grilled cheese"), mother[2] == idx(Mothers, "Aniya")),
    ))

    # Clue 1 (interpreted): The spaghetti eater and Peter are next to each other.
    s.add(Or(
        And(food[0] == idx(Foods, "spaghetti"), name[1] == idx(Names, "Peter")),
        And(food[1] == idx(Foods, "spaghetti"), Or(name[0] == idx(Names, "Peter"), name[2] == idx(Names, "Peter"))),
        And(food[2] == idx(Foods, "spaghetti"), name[1] == idx(Names, "Peter")),
    ))

    assert s.check() == sat, "No solution found"
    m = s.model()

    # Build solution rows in required order 1..3
    rows = []
    for h in houses:
        rows.append([
            str(h + 1),
            Names[m[name[h]].as_long()],
            Mothers[m[mother[h]].as_long()],
            Foods[m[food[h]].as_long()],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    solve()