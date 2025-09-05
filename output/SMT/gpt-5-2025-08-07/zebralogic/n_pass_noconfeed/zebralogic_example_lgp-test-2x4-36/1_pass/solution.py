import json
import re
from z3 import Solver, Int, Distinct, And, sat

def sanitize(s):
    return re.sub(r'[^A-Za-z0-9]+', '_', s)

def main():
    # Houses
    houses = [1, 2]
    N = len(houses)

    # Attributes
    Names = ["Eric", "Arnold"]
    BookGenres = ["science fiction", "mystery"]
    Birthdays = ["april", "sept"]
    Animals = ["horse", "cat"]

    # Z3 Variables: position (house index) for each attribute value
    pos_name = {v: Int(f"pos_name_{sanitize(v)}") for v in Names}
    pos_book = {v: Int(f"pos_book_{sanitize(v)}") for v in BookGenres}
    pos_bday = {v: Int(f"pos_bday_{sanitize(v)}") for v in Birthdays}
    pos_animal = {v: Int(f"pos_animal_{sanitize(v)}") for v in Animals}

    s = Solver()

    # Domain constraints
    for d in (pos_name, pos_book, pos_bday, pos_animal):
        for var in d.values():
            s.add(And(var >= 1, var <= N))

    # Uniqueness constraints (each category is a permutation of houses)
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_book.values()))
    s.add(Distinct(*pos_bday.values()))
    s.add(Distinct(*pos_animal.values()))

    # Clues:
    # 1. Eric is in the first house.
    s.add(pos_name["Eric"] == 1)
    # 2. Eric is the person whose birthday is in September.
    s.add(pos_name["Eric"] == pos_bday["sept"])
    # 3. The person who loves science fiction books is in the second house.
    s.add(pos_book["science fiction"] == 2)
    # 4. The person who keeps horses is the person whose birthday is in September.
    s.add(pos_animal["horse"] == pos_bday["sept"])

    assert s.check() == sat, "Puzzle is unsatisfiable"
    m = s.model()

    def value_at_house(pos_dict, house):
        for val, var in pos_dict.items():
            if m[var].as_long() == house:
                return val
        raise ValueError("No value found for house")

    header = ["House", "Name", "BookGenre", "Birthday", "Animal"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            value_at_house(pos_name, h),
            value_at_house(pos_book, h),
            value_at_house(pos_bday, h),
            value_at_house(pos_animal, h),
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()