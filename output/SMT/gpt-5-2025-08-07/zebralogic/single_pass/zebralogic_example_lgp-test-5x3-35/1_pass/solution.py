import json
from z3 import Int, Solver, Distinct, And

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights = ["average", "very short", "short", "very tall", "tall"]

    # Position variables: each attribute value has a house position (1..5)
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_mother = {m: Int(f"pos_mother_{m}") for m in mothers}
    pos_height = {h: Int(f"pos_height_{h.replace(' ', '_')}") for h in heights}

    s = Solver()

    # Domain constraints: positions are in 1..5
    for v in list(pos_name.values()) + list(pos_mother.values()) + list(pos_height.values()):
        s.add(And(v >= 1, v <= 5))

    # Uniqueness within each attribute type
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_mother.values()))
    s.add(Distinct(*pos_height.values()))

    # Clues:
    # 1. Alice is The person whose mother's name is Aniya.
    s.add(pos_name["Alice"] == pos_mother["Aniya"])

    # 2. average is somewhere to the left of Penny.
    s.add(pos_height["average"] < pos_mother["Penny"])

    # 3. The person whose mother's name is Janelle is Bob.
    s.add(pos_mother["Janelle"] == pos_name["Bob"])

    # 4. Peter is not in the second house.
    s.add(pos_name["Peter"] != 2)

    # 5. short is directly left of Arnold.
    s.add(pos_height["short"] == pos_name["Arnold"] - 1)

    # 6. very tall is Arnold.
    s.add(pos_height["very tall"] == pos_name["Arnold"])

    # 7. Bob is directly left of average.
    s.add(pos_name["Bob"] == pos_height["average"] - 1)

    # 8. Eric is not in the fifth house.
    s.add(pos_name["Eric"] != 5)

    # 9. very tall is somewhere to the right of Holly.
    s.add(pos_height["very tall"] > pos_mother["Holly"])

    # 10. Eric is The person whose mother's name is Kailyn.
    s.add(pos_name["Eric"] == pos_mother["Kailyn"])

    # 11. very short is in the fifth house.
    s.add(pos_height["very short"] == 5)

    assert s.check().r == 1, "Puzzle is unsatisfiable"
    m = s.model()

    # Helper to find label by position
    def label_at_position(pos_map, labels, pos):
        for lbl in labels:
            if m.evaluate(pos_map[lbl]).as_long() == pos:
                return lbl
        return None

    rows = []
    for h in houses:
        name = label_at_position(pos_name, names, h)
        mother = label_at_position(pos_mother, mothers, h)
        height = label_at_position(pos_height, heights, h)
        rows.append([str(h), name, mother, height])

    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))