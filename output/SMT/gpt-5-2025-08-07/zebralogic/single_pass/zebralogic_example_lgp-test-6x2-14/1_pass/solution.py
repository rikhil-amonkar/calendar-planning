import json
from z3 import Int, Solver, Distinct, And, Or, Abs, sat

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]

    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

    def var_name(prefix, label):
        return f"{prefix}_{label.replace(' ', '_').lower()}"

    # Z3 variables: position (house index 1..6) for each name and cigar
    person_pos = {n: Int(var_name("pos_person", n)) for n in names}
    cigar_pos = {c: Int(var_name("pos_cigar", c)) for c in cigars}

    s = Solver()

    # Domain constraints
    for v in list(person_pos.values()) + list(cigar_pos.values()):
        s.add(And(v >= 1, v <= 6))

    # Uniqueness constraints
    s.add(Distinct(*person_pos.values()))
    s.add(Distinct(*cigar_pos.values()))

    # Clues:
    # 1. Arnold is somewhere to the left of the person who smokes many unique blends.
    s.add(person_pos["Arnold"] < cigar_pos["blends"])

    # 2. The person who smokes Blue Master is in the fifth house.
    s.add(cigar_pos["blue master"] == 5)

    # 3. Arnold is somewhere to the left of the Prince smoker.
    s.add(person_pos["Arnold"] < cigar_pos["prince"])

    # 4. There is one house between Yellow Monster and blends.
    s.add(Abs(cigar_pos["yellow monster"] - cigar_pos["blends"]) == 2)

    # 5. Pall Mall is in the third house.
    s.add(cigar_pos["pall mall"] == 3)

    # 6. Eric is in the sixth house.
    s.add(person_pos["Eric"] == 6)

    # 7. Carol and Eric are next to each other.
    s.add(Abs(person_pos["Carol"] - person_pos["Eric"]) == 1)

    # 8. Peter is in the first house.
    s.add(person_pos["Peter"] == 1)

    # 9. Bob is in the third house.
    s.add(person_pos["Bob"] == 3)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build house -> name and house -> cigar mappings
    house_to_name = {}
    for n, v in person_pos.items():
        house_to_name[m[v].as_long()] = n

    house_to_cigar = {}
    for c, v in cigar_pos.items():
        house_to_cigar[m[v].as_long()] = c

    # Prepare JSON output
    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_cigar[h]])

    result = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve_puzzle()