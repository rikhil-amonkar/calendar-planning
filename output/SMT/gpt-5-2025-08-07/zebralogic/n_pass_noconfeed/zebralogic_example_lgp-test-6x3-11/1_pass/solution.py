import json
from z3 import Solver, Int, Distinct, And, Abs, sat

def solve_puzzle():
    houses = list(range(1, 7))

    names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
    hairs = ["auburn", "blonde", "brown", "black", "red", "gray"]
    heights = ["very tall", "average", "very short", "tall", "super tall", "short"]

    # Create Z3 variables for positions of each attribute
    name_pos = {n: Int(f"pos_name_{n}") for n in names}
    hair_pos = {h: Int(f"pos_hair_{h.replace(' ', '_')}") for h in hairs}
    height_pos = {h: Int(f"pos_height_{h.replace(' ', '_')}") for h in heights}

    s = Solver()

    # Domain constraints: all positions are between 1 and 6
    for var in list(name_pos.values()) + list(hair_pos.values()) + list(height_pos.values()):
        s.add(And(var >= 1, var <= 6))

    # Uniqueness constraints within each category
    s.add(Distinct([name_pos[n] for n in names]))
    s.add(Distinct([hair_pos[h] for h in hairs]))
    s.add(Distinct([height_pos[h] for h in heights]))

    # Clues:
    # 1. The person who has blonde hair is directly left of Bob.
    s.add(hair_pos["blonde"] == name_pos["Bob"] - 1)

    # 2. Alice is in the fourth house.
    s.add(name_pos["Alice"] == 4)

    # 3. The person who is short is Arnold.
    s.add(height_pos["short"] == name_pos["Arnold"])

    # 4. The person who is tall is in the sixth house.
    s.add(height_pos["tall"] == 6)

    # 5. The person who has black hair is not in the fourth house.
    s.add(hair_pos["black"] != 4)

    # 6. The person who has red hair is Eric.
    s.add(hair_pos["red"] == name_pos["Eric"])

    # 7. The person who is super tall is somewhere to the right of the person who has an average height.
    s.add(height_pos["super tall"] > height_pos["average"])

    # 8. The person who has blonde hair is Carol.
    s.add(hair_pos["blonde"] == name_pos["Carol"])

    # 9. There is one house between the person who has gray hair and the person who has red hair.
    s.add(Abs(hair_pos["gray"] - hair_pos["red"]) == 2)

    # 10. The person who is very short is in the fifth house.
    s.add(height_pos["very short"] == 5)

    # 11. Bob is the person who has brown hair.
    s.add(name_pos["Bob"] == hair_pos["brown"])

    # 12. The person who has gray hair is in the third house.
    s.add(hair_pos["gray"] == 3)

    # 13. The person who has blonde hair is the person who is very tall.
    s.add(hair_pos["blonde"] == height_pos["very tall"])

    result = {}
    if s.check() == sat:
        m = s.model()

        # Build reverse lookup maps: house -> attribute
        house_to_name = {}
        for n in names:
            house_to_name[m[name_pos[n]].as_long()] = n

        house_to_hair = {}
        for h in hairs:
            house_to_hair[m[hair_pos[h]].as_long()] = h

        house_to_height = {}
        for h in heights:
            house_to_height[m[height_pos[h]].as_long()] = h

        rows = []
        for h in houses:
            rows.append([
                str(h),
                house_to_name[h],
                house_to_hair[h],
                house_to_height[h]
            ])

        result = {
            "solution": {
                "header": ["House", "Name", "HairColor", "Height"],
                "rows": rows
            }
        }
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor", "Height"],
                "rows": []
            }
        }

    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()