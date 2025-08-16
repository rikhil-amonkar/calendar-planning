import json
from z3 import Solver, Int, Distinct, And, Or, Implies, sat

def solve_puzzle():
    # Define domains
    houses = [0, 1]  # 0-based indexing for houses 1..2
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]

    # Indices for specific values
    ARNOLD = names.index("Arnold")
    FRED = children.index("Fred")
    GRILLED = foods.index("grilled cheese")
    PIZZA = foods.index("pizza")

    # Z3 variables: each house gets a name, child, and food (represented as indices)
    name = [Int(f"name_{i}") for i in houses]
    child = [Int(f"child_{i}") for i in houses]
    food = [Int(f"food_{i}") for i in houses]

    s = Solver()

    # Domain constraints (each attribute index is within 0..n-1)
    for i in houses:
        s.add(And(name[i] >= 0, name[i] < len(names)))
        s.add(And(child[i] >= 0, child[i] < len(children)))
        s.add(And(food[i] >= 0, food[i] < len(foods)))

    # Uniqueness constraints: all different across houses for each category
    s.add(Distinct(name))
    s.add(Distinct(child))
    s.add(Distinct(food))

    # Clue 1: The person who is a pizza lover is Arnold.
    for i in houses:
        s.add(Implies(food[i] == PIZZA, name[i] == ARNOLD))
        s.add(Implies(name[i] == ARNOLD, food[i] == PIZZA))

    # Clue 2: The person who loves grilled cheese is directly left of the person whose child is Fred.
    left_constraints = []
    for i in range(len(houses) - 1):
        left_constraints.append(And(food[i] == GRILLED, child[i + 1] == FRED))
    s.add(Or(left_constraints))

    # Solve
    assert s.check() == sat, "No solution found"
    m = s.model()

    # Build the output rows in house order (1-based labels)
    rows = []
    for i in houses:
        rows.append([
            str(i + 1),
            names[m.evaluate(name[i]).as_long()],
            children[m.evaluate(child[i]).as_long()],
            foods[m.evaluate(food[i]).as_long()],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()