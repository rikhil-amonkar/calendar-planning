import json
from z3 import Int, Solver, And, Distinct, sat

def solve_puzzle():
    houses = [1, 2, 3]

    names = ["Eric", "Arnold", "Peter"]
    book_genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]

    # Create Z3 Int variables for positions (1..3)
    pos_name = {n: Int(f"name_{n}") for n in names}
    pos_genre = {g: Int(f"genre_{g.replace(' ', '_')}") for g in book_genres}
    pos_vac = {v: Int(f"vac_{v}") for v in vacations}

    s = Solver()

    # Domain constraints
    for d in (pos_name, pos_genre, pos_vac):
        for var in d.values():
            s.add(And(var >= 1, var <= 3))

    # All-different within each category
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_genre.values()))
    s.add(Distinct(*pos_vac.values()))

    # Clue 1: Eric is directly left of Arnold.
    s.add(pos_name["Eric"] + 1 == pos_name["Arnold"])

    # Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
    s.add(pos_name["Peter"] > pos_vac["beach"])

    # Clue 3: Peter is the person who prefers city breaks.
    s.add(pos_name["Peter"] == pos_vac["city"])

    # Clue 4: Mystery is to the left of Beach.
    s.add(pos_genre["mystery"] < pos_vac["beach"])

    # Clue 5: Science fiction == Beach.
    s.add(pos_genre["science fiction"] == pos_vac["beach"])

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Invert mappings: for each house, find the name/genre/vacation located there
    house_to_name = {}
    house_to_genre = {}
    house_to_vac = {}

    for n, var in pos_name.items():
        house_to_name[m[var].as_long()] = n
    for g, var in pos_genre.items():
        house_to_genre[m[var].as_long()] = g
    for v, var in pos_vac.items():
        house_to_vac[m[var].as_long()] = v

    rows = []
    for h in houses:
        rows.append([
            str(h),
            house_to_name[h],
            house_to_genre[h],
            house_to_vac[h],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation"],
            "rows": rows
        }
    }

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()