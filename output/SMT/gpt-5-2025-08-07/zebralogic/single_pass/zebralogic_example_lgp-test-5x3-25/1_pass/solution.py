import json
from z3 import Int, Solver, And, Distinct, Implies

def solve():
    houses = range(5)  # 0..4 representing houses 1..5

    # Domains
    names = ["Arnold", "Bob", "Alice", "Eric", "Peter"]
    heights = ["very tall", "average", "tall", "very short", "short"]
    foods = ["stew", "grilled cheese", "spaghetti", "pizza", "stir fry"]

    name_idx = {v: i for i, v in enumerate(names)}
    height_idx = {v: i for i, v in enumerate(heights)}
    food_idx = {v: i for i, v in enumerate(foods)}

    # Variables: for each house, assign an index into names/heights/foods
    name_vars = [Int(f"name_{i}") for i in houses]
    height_vars = [Int(f"height_{i}") for i in houses]
    food_vars = [Int(f"food_{i}") for i in houses]

    s = Solver()

    # Domain constraints
    for i in houses:
        s.add(And(name_vars[i] >= 0, name_vars[i] < len(names)))
        s.add(And(height_vars[i] >= 0, height_vars[i] < len(heights)))
        s.add(And(food_vars[i] >= 0, food_vars[i] < len(foods)))

    # All-different constraints per attribute
    s.add(Distinct(name_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(food_vars))

    # Clues:
    # 1. Alice is the person who is short.
    for i in houses:
        s.add(Implies(name_vars[i] == name_idx["Alice"], height_vars[i] == height_idx["short"]))

    # 2. The person who is tall is in the third house. (house index 2)
    s.add(height_vars[2] == height_idx["tall"])

    # 3. The person who has an average height is not in the second house. (house index 1)
    s.add(height_vars[1] != height_idx["average"])

    # 4. The person who has an average height is somewhere to the left of the person who loves the stew.
    for i in houses:
        for j in houses:
            s.add(Implies(And(height_vars[i] == height_idx["average"], food_vars[j] == food_idx["stew"]), i < j))

    # 5. The person who loves stir fry is Arnold.
    for i in houses:
        s.add(Implies(name_vars[i] == name_idx["Arnold"], food_vars[i] == food_idx["stir fry"]))

    # 6. The person who is a pizza lover is the person who is tall. (iff)
    for i in houses:
        s.add((height_vars[i] == height_idx["tall"]) == (food_vars[i] == food_idx["pizza"]))

    # 7. Eric is the person who is tall.
    for i in houses:
        s.add(Implies(name_vars[i] == name_idx["Eric"], height_vars[i] == height_idx["tall"]))

    # 8. Bob is somewhere to the right of Arnold.
    for i in houses:
        for j in houses:
            s.add(Implies(And(name_vars[i] == name_idx["Arnold"], name_vars[j] == name_idx["Bob"]), i < j))

    # 9. The person who loves eating grilled cheese is somewhere to the right of Eric.
    for i in houses:
        for j in houses:
            s.add(Implies(And(name_vars[i] == name_idx["Eric"], food_vars[j] == food_idx["grilled cheese"]), i < j))

    # 10. The person who is very short is somewhere to the left of Arnold.
    for i in houses:
        for j in houses:
            s.add(Implies(And(height_vars[i] == height_idx["very short"], name_vars[j] == name_idx["Arnold"]), i < j))

    if s.check() != z3.sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build solution rows in order of houses 1..5 (indices 0..4)
    rows = []
    for i in houses:
        name = names[m[name_vars[i]].as_long()]
        height = heights[m[height_vars[i]].as_long()]
        food = foods[m[food_vars[i]].as_long()]
        rows.append([str(i + 1), name, height, food])

    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    # Ensure z3 is imported into the namespace for the sat check above
    import z3  # noqa: F401
    solve()