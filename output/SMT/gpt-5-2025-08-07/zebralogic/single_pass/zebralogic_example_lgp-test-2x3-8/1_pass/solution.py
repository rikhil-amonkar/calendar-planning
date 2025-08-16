import json
from z3 import Int, Solver, Distinct, And, Or, sat

def solve_puzzle():
    # Enumerations
    Names = ['Arnold', 'Eric']
    Birthdays = ['april', 'sept']
    Mothers = ['Aniya', 'Holly']

    NAME = {v: i for i, v in enumerate(Names)}
    BDAY = {v: i for i, v in enumerate(Birthdays)}
    MOM = {v: i for i, v in enumerate(Mothers)}

    H = 2  # number of houses

    # Variables per house
    name = [Int(f"name_{i}") for i in range(H)]
    bday = [Int(f"bday_{i}") for i in range(H)]
    mother = [Int(f"mother_{i}") for i in range(H)]

    s = Solver()

    # Domains
    for i in range(H):
        s.add(name[i] >= 0, name[i] < len(Names))
        s.add(bday[i] >= 0, bday[i] < len(Birthdays))
        s.add(mother[i] >= 0, mother[i] < len(Mothers))

    # Uniqueness across houses
    s.add(Distinct(name))
    s.add(Distinct(bday))
    s.add(Distinct(mother))

    # Clue 2: The person whose birthday is in April is in the first house.
    s.add(bday[0] == BDAY['april'])

    # Clue 1: Eric is somewhere to the left of the person whose mother's name is Holly.
    pos_eric = Int("pos_eric")
    pos_holly_mom = Int("pos_holly_mom")
    s.add(pos_eric >= 0, pos_eric < H)
    s.add(pos_holly_mom >= 0, pos_holly_mom < H)

    s.add(Or(*[And(pos_eric == i, name[i] == NAME['Eric']) for i in range(H)]))
    s.add(Or(*[And(pos_holly_mom == i, mother[i] == MOM['Holly']) for i in range(H)]))
    s.add(pos_eric < pos_holly_mom)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    rows = []
    for i in range(H):
        row = [
            str(i + 1),
            Names[m[name[i]].as_long()],
            Birthdays[m[bday[i]].as_long()],
            Mothers[m[mother[i]].as_long()],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()