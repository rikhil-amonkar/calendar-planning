import json
from z3 import Solver, Int, And, Or, Distinct, Abs, sat

def solve_puzzle():
    # Houses (1..3), Names, Heights
    houses = [1, 2, 3]
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]

    # Map attributes to integer IDs
    name_ids = {n: i for i, n in enumerate(names)}
    height_ids = {h: i for i, h in enumerate(heights)}

    # Z3 variables: assignments per house (index 0 -> house 1)
    Name = [Int(f"name_{i+1}") for i in range(3)]
    Height = [Int(f"height_{i+1}") for i in range(3)]

    s = Solver()

    # Domains
    for i in range(3):
        s.add(And(Name[i] >= 0, Name[i] < len(names)))
        s.add(And(Height[i] >= 0, Height[i] < len(heights)))

    # All attributes are unique across houses
    s.add(Distinct(Name))
    s.add(Distinct(Height))

    # Position variables for names and heights (house index 1..3)
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_height = {h: Int(f"pos_height_{h.replace(' ', '_')}") for h in heights}

    for n in names:
        s.add(And(pos_name[n] >= 1, pos_name[n] <= 3))
        s.add(Or(*[And(Name[i] == name_ids[n], pos_name[n] == i + 1) for i in range(3)]))

    for h in heights:
        s.add(And(pos_height[h] >= 1, pos_height[h] <= 3))
        s.add(Or(*[And(Height[i] == height_ids[h], pos_height[h] == i + 1) for i in range(3)]))

    # Clues:
    # 1. Peter is somewhere to the right of Eric.
    s.add(pos_name["Peter"] > pos_name["Eric"])

    # 2. The person who is short is in the first house.
    s.add(Height[0] == height_ids["short"])

    # 3. There is one house between the person who is short and the person who is very short.
    s.add(Abs(pos_height["short"] - pos_height["very short"]) == 2)

    # 4. Arnold and the person who is very short are next to each other.
    s.add(Abs(pos_name["Arnold"] - pos_height["very short"]) == 1)

    # Solve and prepare JSON output
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(3):
            name_val = names[m[Name[i]].as_long()]
            height_val = heights[m[Height[i]].as_long()]
            rows.append([str(i + 1), name_val, height_val])

        result = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
    else:
        result = {"solution": {"header": ["House", "Name", "Height"], "rows": []}}

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))