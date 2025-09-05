import json
from z3 import Solver, Int, Distinct, And, Or

def solve_puzzle():
    # Define domains
    houses = [1, 2]  # House numbers from left to right
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]

    # Map attributes to indices for Z3
    name_to_idx = {name: i for i, name in enumerate(names)}
    food_to_idx = {food: i for i, food in enumerate(foods)}

    # Create Z3 variables for each house's attributes
    name_vars = [Int(f"name_{h}") for h in houses]
    food_vars = [Int(f"food_{h}") for h in houses]

    s = Solver()

    # Domain constraints
    for nv in name_vars:
        s.add(Or([nv == i for i in range(len(names))]))
    for fv in food_vars:
        s.add(Or([fv == i for i in range(len(foods))]))

    # Uniqueness constraints
    s.add(Distinct(name_vars))
    s.add(Distinct(food_vars))

    # Clues:
    # 1. The person who is a pizza lover is in the second house.
    s.add(food_vars[houses.index(2)] == food_to_idx["pizza"])

    # 2. Arnold is not in the first house.
    s.add(name_vars[houses.index(1)] != name_to_idx["Arnold"])

    if s.check() != 1:  # sat
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build solution rows in house order
    rows = []
    for h in houses:
        name_idx = m[name_vars[houses.index(h)]].as_long()
        food_idx = m[food_vars[houses.index(h)]].as_long()
        rows.append([str(h), names[name_idx], foods[food_idx]])

    result = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))