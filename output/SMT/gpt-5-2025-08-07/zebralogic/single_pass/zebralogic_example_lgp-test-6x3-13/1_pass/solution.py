import json
from z3 import Solver, Int, And, Or, Distinct, sat

def make_pos_vars(labels, prefix):
    # Create Z3 Int vars for positions (1..6) of each label
    vars_dict = {}
    for lbl in labels:
        var_name = f"{prefix}_" + lbl.replace(" ", "_")
        vars_dict[lbl] = Int(var_name)
    return vars_dict

def constrain_domain_and_distinct(s, vars_dict, n_houses):
    # Each variable is in [1, n_houses] and all are distinct
    s.add([And(v >= 1, v <= n_houses) for v in vars_dict.values()])
    s.add(Distinct(list(vars_dict.values())))

def invert_position(model, pos_dict, house):
    # Find which label is at the given house index
    for lbl, var in pos_dict.items():
        if model[var].as_long() == house:
            return lbl
    return None

def main():
    n_houses = 6

    # Attributes
    names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
    books = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
    occs  = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

    # Create position variables
    pos_name = make_pos_vars(names, "name")
    pos_book = make_pos_vars(books, "book")
    pos_occ  = make_pos_vars(occs,  "occ")

    s = Solver()

    # Domain and distinctness constraints
    constrain_domain_and_distinct(s, pos_name, n_houses)
    constrain_domain_and_distinct(s, pos_book, n_houses)
    constrain_domain_and_distinct(s, pos_occ,  n_houses)

    # Clues encoding:

    # 1. Alice is the person who loves fantasy books.
    s.add(pos_name["Alice"] == pos_book["fantasy"])

    # 2. The person who loves mystery books and Bob are next to each other.
    s.add(Or(pos_book["mystery"] == pos_name["Bob"] + 1,
             pos_book["mystery"] == pos_name["Bob"] - 1))

    # 3. Carol is the person who loves mystery books.
    s.add(pos_name["Carol"] == pos_book["mystery"])

    # 4. The person who is a lawyer is the person who loves fantasy books.
    s.add(pos_occ["lawyer"] == pos_book["fantasy"])

    # 5. Bob is not in the fifth house.
    s.add(pos_name["Bob"] != 5)

    # 6. Arnold is somewhere to the left of the person who is an engineer.
    s.add(pos_name["Arnold"] < pos_occ["engineer"])

    # 7. The person who is a nurse is directly left of Alice.
    s.add(pos_occ["nurse"] + 1 == pos_name["Alice"])

    # 8. The person who loves biography books is the person who is a teacher.
    s.add(pos_book["biography"] == pos_occ["teacher"])

    # 9. The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    s.add(pos_book["historical fiction"] < pos_occ["teacher"])

    # 10. The person who is a doctor is in the first house.
    s.add(pos_occ["doctor"] == 1)

    # 11. The person who loves science fiction books is the person who is an artist.
    s.add(pos_book["science fiction"] == pos_occ["artist"])

    # 12. Eric is in the third house.
    s.add(pos_name["Eric"] == 3)

    # 13. The person who loves mystery books is not in the fifth house.
    s.add(pos_book["mystery"] != 5)

    # Solve
    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build solution rows in order of houses 1..6
    rows = []
    for h in range(1, n_houses + 1):
        name = invert_position(m, pos_name, h)
        book = invert_position(m, pos_book, h)
        occ  = invert_position(m, pos_occ,  h)
        rows.append([str(h), name, book, occ])

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()