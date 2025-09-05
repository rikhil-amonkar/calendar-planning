import json
from z3 import Int, Solver, Distinct, And, Or, Abs

def solve_puzzle():
    houses = range(1, 7)  # 1..6

    # Attributes
    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

    # Variables: position (house number) for each attribute value
    pos_name = {n: Int(f"pos_name_{n.lower()}") for n in names}
    pos_cigar = {c: Int(f"pos_cigar_{c.replace(' ', '_')}") for c in cigars}

    s = Solver()

    # Domains: 1..6
    for v in pos_name.values():
        s.add(And(v >= 1, v <= 6))
    for v in pos_cigar.values():
        s.add(And(v >= 1, v <= 6))

    # All different within each category
    s.add(Distinct(list(pos_name.values())))
    s.add(Distinct(list(pos_cigar.values())))

    # Clues:
    # 1. Arnold is somewhere to the left of the person who smokes many unique blends.
    s.add(pos_name["Arnold"] < pos_cigar["blends"])

    # 2. The person who smokes Blue Master is in the fifth house.
    s.add(pos_cigar["blue master"] == 5)

    # 3. Arnold is somewhere to the left of the Prince smoker.
    s.add(pos_name["Arnold"] < pos_cigar["prince"])

    # 4. There is one house between Yellow Monster and blends.
    s.add(Abs(pos_cigar["yellow monster"] - pos_cigar["blends"]) == 2)

    # 5. Pall Mall is in the third house.
    s.add(pos_cigar["pall mall"] == 3)

    # 6. Eric is in the sixth house.
    s.add(pos_name["Eric"] == 6)

    # 7. Carol and Eric are next to each other.
    s.add(Abs(pos_name["Carol"] - pos_name["Eric"]) == 1)

    # 8. Peter is in the first house.
    s.add(pos_name["Peter"] == 1)

    # 9. Bob is in the third house.
    s.add(pos_name["Bob"] == 3)

    assert s.check().r == 1, "Puzzle is unsatisfiable"
    m = s.model()

    # Invert mappings to get attributes by house
    name_by_house = {m.evaluate(v).as_long(): k for k, v in pos_name.items()}
    cigar_by_house = {m.evaluate(v).as_long(): k for k, v in pos_cigar.items()}

    rows = []
    for h in houses:
        rows.append([str(h), name_by_house[h], cigar_by_house[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))