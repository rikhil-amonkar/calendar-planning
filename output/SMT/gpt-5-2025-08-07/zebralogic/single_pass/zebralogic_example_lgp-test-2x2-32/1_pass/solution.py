from z3 import Int, Solver, Distinct, And, sat
import json

def sanitize(label):
    return ''.join(c if c.isalnum() else '_' for c in label)

def solve_puzzle():
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    genres = ["science fiction", "mystery"]

    # Create Z3 variables for positions of each name and genre
    pos_name = {n: Int(f"pos_name_{sanitize(n)}") for n in names}
    pos_genre = {g: Int(f"pos_genre_{sanitize(g)}") for g in genres}

    s = Solver()

    # Domain constraints: each position is a house number 1..2
    for v in list(pos_name.values()) + list(pos_genre.values()):
        s.add(And(v >= 1, v <= 2))

    # Uniqueness constraints: each name/genre occupies a unique house
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_genre.values()))

    # Clue: 1) Eric is directly left of the person who loves mystery books.
    s.add(pos_name["Eric"] + 1 == pos_genre["mystery"])

    assert s.check() == sat, "Puzzle is unsatisfiable"
    m = s.model()

    # Build solution rows in house order
    rows = []
    for h in houses:
        # Find the name and genre assigned to house h
        name_at_h = next(n for n, v in pos_name.items() if m[v].as_long() == h)
        genre_at_h = next(g for g, v in pos_genre.items() if m[v].as_long() == h)
        rows.append([str(h), name_at_h, genre_at_h])

    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": rows
        }
    }
    return solution

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))