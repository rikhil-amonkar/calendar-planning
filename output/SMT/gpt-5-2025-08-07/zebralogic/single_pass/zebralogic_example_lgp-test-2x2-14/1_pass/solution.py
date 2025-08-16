from z3 import Int, Solver, Distinct, Or, sat
import json

def solve_puzzle():
    # Domains
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]

    # Z3 variables: map each attribute value to a house number
    name_vars = {n: Int(f"house_of_name_{n}") for n in names}
    food_vars = {f: Int(f"house_of_food_{f.replace(' ', '_')}") for f in foods}

    s = Solver()

    # Domain constraints: each variable is one of the house indices
    for v in list(name_vars.values()) + list(food_vars.values()):
        s.add(Or([v == h for h in houses]))

    # Uniqueness: each house has exactly one name and one food
    s.add(Distinct(*name_vars.values()))
    s.add(Distinct(*food_vars.values()))

    # Clues:
    # 1. The person who is a pizza lover is in the second house.
    s.add(food_vars["pizza"] == 2)
    # 2. Arnold is not in the first house.
    s.add(name_vars["Arnold"] != 1)

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    # Build house -> attribute mappings
    house_to_name = {}
    for n, var in name_vars.items():
        house_to_name[m[var].as_long()] = n

    house_to_food = {}
    for f, var in food_vars.items():
        house_to_food[m[var].as_long()] = f

    # Construct required JSON structure
    result = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": []
        }
    }

    for h in houses:
        row = [str(h), house_to_name[h], house_to_food[h]]
        result["solution"]["rows"].append(row)

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()