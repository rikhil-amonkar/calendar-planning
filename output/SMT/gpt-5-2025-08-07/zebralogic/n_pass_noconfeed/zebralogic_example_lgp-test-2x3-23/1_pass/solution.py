import json
from z3 import Solver, Int, And, Distinct, sat

def main():
    # Houses
    houses = [1, 2]
    N = len(houses)

    # Attributes
    Names = ["Eric", "Arnold"]
    Children = ["Bella", "Fred"]
    Foods = ["grilled cheese", "pizza"]

    # Z3 Variables: each attribute value maps to a house number
    name_vars = {n: Int(f"name_{n}") for n in Names}
    child_vars = {c: Int(f"child_{c}") for c in Children}
    food_vars = {f: Int(f"food_{f.replace(' ', '_')}") for f in Foods}

    s = Solver()

    # Domain constraints and bijectivity for each category
    for vars_dict in [name_vars, child_vars, food_vars]:
        vars_list = list(vars_dict.values())
        for v in vars_list:
            s.add(And(v >= 1, v <= N))
        s.add(Distinct(vars_list))

    # Clue 1: The person who is a pizza lover is Arnold.
    s.add(food_vars["pizza"] == name_vars["Arnold"])

    # Clue 2: The person who loves eating grilled cheese is directly left of
    # the person whose child is named Fred.
    s.add(food_vars["grilled cheese"] + 1 == child_vars["Fred"])

    # Solve
    if s.check() != sat:
        raise RuntimeError("Puzzle constraints are unsatisfiable.")
    m = s.model()

    # Helper to invert mapping: house -> attribute value
    def invert(vars_dict):
        res = {}
        for val, var in vars_dict.items():
            h = m[var].as_long()
            res[h] = val
        return res

    house_to_name = invert(name_vars)
    house_to_child = invert(child_vars)
    house_to_food = invert(food_vars)

    rows = []
    for h in houses:
        rows.append([str(h), house_to_name[h], house_to_child[h], house_to_food[h]])

    output = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()