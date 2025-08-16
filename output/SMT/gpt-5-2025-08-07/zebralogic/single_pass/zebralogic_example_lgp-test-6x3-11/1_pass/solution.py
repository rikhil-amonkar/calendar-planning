import json
from z3 import Solver, Int, Distinct, And, Or

def solve_puzzle():
    houses = range(1, 7)

    names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
    hair_colors = ["auburn", "blonde", "brown", "black", "red", "gray"]
    heights = ["very tall", "average", "very short", "tall", "super tall", "short"]

    # Position variables for each attribute (house numbers 1..6)
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_hair = {h: Int(f"pos_hair_{h.replace(' ', '_')}") for h in hair_colors}
    pos_height = {h: Int(f"pos_height_{h.replace(' ', '_')}") for h in heights}

    s = Solver()

    # Domains: all positions between 1 and 6
    for v in list(pos_name.values()) + list(pos_hair.values()) + list(pos_height.values()):
        s.add(And(v >= 1, v <= 6))

    # Uniqueness within each category
    s.add(Distinct(*pos_name.values()))
    s.add(Distinct(*pos_hair.values()))
    s.add(Distinct(*pos_height.values()))

    # Clues:
    # 1. Blonde is directly left of Bob.
    s.add(pos_hair["blonde"] + 1 == pos_name["Bob"])

    # 2. Alice is in the fourth house.
    s.add(pos_name["Alice"] == 4)

    # 3. The person who is short is Arnold.
    s.add(pos_name["Arnold"] == pos_height["short"])

    # 4. Tall is in the sixth house.
    s.add(pos_height["tall"] == 6)

    # 5. Black hair is not in the fourth house.
    s.add(pos_hair["black"] != 4)

    # 6. Red hair is Eric.
    s.add(pos_hair["red"] == pos_name["Eric"])

    # 7. Super tall is somewhere to the right of average.
    s.add(pos_height["super tall"] > pos_height["average"])

    # 8. Blonde hair is Carol.
    s.add(pos_hair["blonde"] == pos_name["Carol"])

    # 9. One house between gray hair and red hair.
    s.add(Or(pos_hair["gray"] == pos_hair["red"] + 2,
             pos_hair["gray"] == pos_hair["red"] - 2))

    # 10. Very short is in the fifth house.
    s.add(pos_height["very short"] == 5)

    # 11. Bob has brown hair.
    s.add(pos_name["Bob"] == pos_hair["brown"])

    # 12. Gray hair is in the third house.
    s.add(pos_hair["gray"] == 3)

    # 13. Blonde hair is very tall.
    s.add(pos_hair["blonde"] == pos_height["very tall"])

    if s.check() != 1:  # sat == 1
        raise RuntimeError("No solution found")

    m = s.model()

    # Build result per house
    rows = []
    for h in houses:
        name_at_h = next(n for n in names if m[pos_name[n]].as_long() == h)
        hair_at_h = next(c for c in hair_colors if m[pos_hair[c]].as_long() == h)
        height_at_h = next(ht for ht in heights if m[pos_height[ht]].as_long() == h)
        rows.append([str(h), name_at_h, hair_at_h, height_at_h])

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()