from z3 import Solver, Int, Distinct, And, sat
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]

    Names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    Heights = ["very tall", "average", "tall", "very short", "short"]
    Foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    # Position variables: each item maps to a house index (1..5)
    pos_name = {n: Int(f"pos_name_{n.replace(' ', '_')}") for n in Names}
    pos_height = {h: Int(f"pos_height_{h.replace(' ', '_')}") for h in Heights}
    pos_food = {f: Int(f"pos_food_{f.replace(' ', '_')}") for f in Foods}

    s = Solver()

    # Domain constraints
    for d in [pos_name, pos_height, pos_food]:
        for v in d.values():
            s.add(And(v >= 1, v <= 5))

    # All-different constraints within each category
    s.add(Distinct(list(pos_name.values())))
    s.add(Distinct(list(pos_height.values())))
    s.add(Distinct(list(pos_food.values())))

    # Clues:
    # 1. Alice is the person who is short.
    s.add(pos_name["Alice"] == pos_height["short"])

    # 2. The person who is tall is in the third house.
    s.add(pos_height["tall"] == 3)

    # 3. The person who has an average height is not in the second house.
    s.add(pos_height["average"] != 2)

    # 4. The person who has an average height is somewhere to the left of the person who loves the stew.
    s.add(pos_height["average"] < pos_food["stew"])

    # 5. The person who loves stir fry is Arnold.
    s.add(pos_name["Arnold"] == pos_food["stir fry"])

    # 6. The person who is a pizza lover is the person who is tall.
    s.add(pos_food["pizza"] == pos_height["tall"])

    # 7. Eric is the person who is tall.
    s.add(pos_name["Eric"] == pos_height["tall"])

    # 8. Bob is somewhere to the right of Arnold.
    s.add(pos_name["Bob"] > pos_name["Arnold"])

    # 9. The person who loves eating grilled cheese is somewhere to the right of Eric.
    s.add(pos_food["grilled cheese"] > pos_name["Eric"])

    # 10. The person who is very short is somewhere to the left of Arnold.
    s.add(pos_height["very short"] < pos_name["Arnold"])

    if s.check() != sat:
        # Fallback JSON if unsat (should not happen with correct clues)
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "Food"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    m = s.model()

    # Build mappings from house -> attribute
    house_to_name = {}
    for k, v in pos_name.items():
        house_to_name[m[v].as_long()] = k

    house_to_height = {}
    for k, v in pos_height.items():
        house_to_height[m[v].as_long()] = k

    house_to_food = {}
    for k, v in pos_food.items():
        house_to_food[m[v].as_long()] = k

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_height[h], house_to_food[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()