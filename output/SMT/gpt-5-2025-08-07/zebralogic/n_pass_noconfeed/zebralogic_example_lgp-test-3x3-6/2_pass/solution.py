import json
from z3 import Solver, Int, Distinct, And, sat

def solve_puzzle():
    houses = [1, 2, 3]

    Names = ["Eric", "Arnold", "Peter"]
    BookGenres = ["mystery", "science fiction", "romance"]
    Vacations = ["mountain", "beach", "city"]

    # Create Z3 variables representing the house position (1..3) for each attribute value
    name_pos = {n: Int(f"name_{n}") for n in Names}
    genre_pos = {g: Int(f"genre_{g.replace(' ', '_')}") for g in BookGenres}
    vacation_pos = {v: Int(f"vacation_{v}") for v in Vacations}

    s = Solver()

    # Domain constraints: all positions are in 1..3
    for d in [name_pos, genre_pos, vacation_pos]:
        for var in d.values():
            s.add(And(var >= 1, var <= 3))

    # Uniqueness constraints within each category
    s.add(Distinct(*name_pos.values()))
    s.add(Distinct(*genre_pos.values()))
    s.add(Distinct(*vacation_pos.values()))

    # Clues:
    # 1. Eric is directly left of Arnold.
    s.add(name_pos["Eric"] + 1 == name_pos["Arnold"])

    # 2. Peter is somewhere to the right of the person who loves beach vacations.
    s.add(name_pos["Peter"] > vacation_pos["beach"])

    # 3. Peter is the person who prefers city breaks.
    s.add(name_pos["Peter"] == vacation_pos["city"])

    # 4. The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
    s.add(genre_pos["mystery"] < vacation_pos["beach"])

    # 5. The person who loves science fiction books is the person who loves beach vacations.
    s.add(genre_pos["science fiction"] == vacation_pos["beach"])

    # Correct check for satisfiability
    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build reverse mappings from house -> attribute value
    pos_to_name = {m.eval(v).as_long(): k for k, v in name_pos.items()}
    pos_to_genre = {m.eval(v).as_long(): k for k, v in genre_pos.items()}
    pos_to_vac = {m.eval(v).as_long(): k for k, v in vacation_pos.items()}

    rows = []
    for h in houses:
        rows.append([
            str(h),
            pos_to_name[h],
            pos_to_genre[h],
            pos_to_vac[h],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))