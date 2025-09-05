import json
from z3 import *

def main():
    # Create a Z3 solver instance
    s = Solver()

    # Define houses
    houses = [1, 2]

    # For each house, define a variable for Name and Food.
    # Domain for Name: 0 (Arnold) and 1 (Eric)
    names = [Int(f"name_{h}") for h in houses]
    # Domain for Food: 0 (pizza) and 1 (grilled cheese)
    foods = [Int(f"food_{h}") for h in houses]

    # Add domain constraints: each must be either 0 or 1
    for n in names:
        s.add(Or(n == 0, n == 1))
    for f in foods:
        s.add(Or(f == 0, f == 1))

    # Since each house has a unique name and unique food, add distinct constraints.
    s.add(Distinct(names))
    s.add(Distinct(foods))

    # Clue 1: The person who is a pizza lover is in the second house.
    # Mapping for Food: 0 -> pizza, 1 -> grilled cheese
    s.add(foods[1] == 0)

    # Clue 2: Arnold is not in the first house.
    # Mapping for Name: 0 -> Arnold, 1 -> Eric
    s.add(names[0] != 0)

    # Check for satisfiability and retrieve the model if possible.
    if s.check() == sat:
        m = s.model()

        # Define mappings to convert integer values to their corresponding names and foods.
        name_mapping = {0: "Arnold", 1: "Eric"}
        food_mapping = {0: "pizza", 1: "grilled cheese"}

        # Build solution rows based on the houses order.
        solution_rows = []
        for idx, h in enumerate(houses):
            house_str = str(h)
            name_val = name_mapping[m.evaluate(names[idx]).as_long()]
            food_val = food_mapping[m.evaluate(foods[idx]).as_long()]
            solution_rows.append([house_str, name_val, food_val])

        # Construct the final JSON result as a Python dictionary.
        result = {
            "solution": {
                "header": ["House", "Name", "Food"],
                "rows": solution_rows
            }
        }
        # Output the JSON-formatted result.
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()