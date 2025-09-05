import json
from z3 import Solver, Int, Distinct, And

def sanitize(s):
    return ''.join(ch if ch.isalnum() else '_' for ch in s)

def main():
    # Puzzle parameters
    houses = [1, 2]  # House numbers from left (1) to right (2)
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]

    H = len(houses)

    # Create Z3 solver
    s = Solver()

    # Position variables: position of each attribute value (which house it is in)
    pos_name = {n: Int(f"pos_name_{sanitize(n)}") for n in names}
    pos_book = {b: Int(f"pos_book_{sanitize(b)}") for b in book_genres}

    # Domain constraints: positions are in [1..H]
    for v in pos_name.values():
        s.add(And(v >= 1, v <= H))
    for v in pos_book.values():
        s.add(And(v >= 1, v <= H))

    # All-different constraints within each category
    s.add(Distinct(list(pos_name.values())))
    s.add(Distinct(list(pos_book.values())))

    # Clue 1: Eric is directly left of the person who loves mystery books.
    s.add(pos_name["Eric"] + 1 == pos_book["mystery"])

    # Solve
    if s.check() != 1:  # 1 corresponds to sat
        raise RuntimeError("No solution found for the given puzzle.")

    m = s.model()

    # Build solution rows per house
    rows = []
    for h in houses:
        # Determine the unique name at house h
        house_name = next(n for n in names if m.eval(pos_name[n]).as_long() == h)
        # Determine the unique book genre at house h
        house_book = next(b for b in book_genres if m.eval(pos_book[b]).as_long() == h)
        rows.append([str(h), house_name, house_book])

    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()