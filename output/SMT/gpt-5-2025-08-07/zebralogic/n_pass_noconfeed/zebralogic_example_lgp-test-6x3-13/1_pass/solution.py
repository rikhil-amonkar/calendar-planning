import json
from z3 import Solver, Int, Distinct, And, Or, Abs

def solve_puzzle():
    houses = list(range(1, 7))

    # Attributes
    names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
    book_genres = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
    occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

    # Create Z3 variables mapping each attribute value to a house number (1..6)
    name_vars = {n: Int(f"house_of_name_{n}") for n in names}
    book_vars = {b: Int(f"house_of_book_{b.replace(' ', '_')}") for b in book_genres}
    occ_vars = {o: Int(f"house_of_occ_{o.replace(' ', '_')}") for o in occupations}

    s = Solver()

    # Domain constraints
    for v in list(name_vars.values()) + list(book_vars.values()) + list(occ_vars.values()):
        s.add(And(v >= 1, v <= 6))

    # Uniqueness within each category
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*book_vars.values()))
    s.add(Distinct(*occ_vars.values()))

    # Clues:
    # 1. Alice is the person who loves fantasy books.
    s.add(name_vars["Alice"] == book_vars["fantasy"])

    # 2. The person who loves mystery books and Bob are next to each other.
    # 3. Carol is the person who loves mystery books.
    s.add(name_vars["Carol"] == book_vars["mystery"])
    s.add(Abs(book_vars["mystery"] - name_vars["Bob"]) == 1)

    # 4. The person who is a lawyer is the person who loves fantasy books.
    s.add(occ_vars["lawyer"] == book_vars["fantasy"])

    # 5. Bob is not in the fifth house.
    s.add(name_vars["Bob"] != 5)

    # 6. Arnold is somewhere to the left of the person who is an engineer.
    s.add(name_vars["Arnold"] < occ_vars["engineer"])

    # 7. The person who is a nurse is directly left of Alice.
    s.add(occ_vars["nurse"] + 1 == name_vars["Alice"])

    # 8. The person who loves biography books is the person who is a teacher.
    s.add(book_vars["biography"] == occ_vars["teacher"])

    # 9. The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    s.add(book_vars["historical fiction"] < occ_vars["teacher"])

    # 10. The person who is a doctor is in the first house.
    s.add(occ_vars["doctor"] == 1)

    # 11. The person who loves science fiction books is the person who is an artist.
    s.add(book_vars["science fiction"] == occ_vars["artist"])

    # 12. Eric is in the third house.
    s.add(name_vars["Eric"] == 3)

    # 13. The person who loves mystery books is not in the fifth house.
    s.add(book_vars["mystery"] != 5)

    if s.check() != 1:  # 1 corresponds to sat in z3
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build rows for each house
    def find_by_house(mapping, house):
        for key, var in mapping.items():
            if m.evaluate(var).as_long() == house:
                return key
        return None

    rows = []
    for h in houses:
        nm = find_by_house(name_vars, h)
        bk = find_by_house(book_vars, h)
        oc = find_by_house(occ_vars, h)
        rows.append([str(h), nm, bk, oc])

    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))