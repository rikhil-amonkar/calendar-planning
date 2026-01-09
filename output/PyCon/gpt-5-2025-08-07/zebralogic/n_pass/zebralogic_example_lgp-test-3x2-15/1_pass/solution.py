import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define attributes
    houses = [1, 2, 3]
    names = ["Arnold", "Peter", "Eric"]
    heights = ["short", "average", "very short"]

    problem = Problem()

    # Variables for names: position of each person
    for name in names:
        problem.addVariable(f"pos_{name}", houses)
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{n}" for n in names])

    # Variables for heights: position of each height
    height_var_map = {h: f"h_{h.replace(' ', '_')}" for h in heights}
    for h, var in height_var_map.items():
        problem.addVariable(var, houses)
    problem.addConstraint(AllDifferentConstraint(), list(height_var_map.values()))

    # Constraints:
    # 1. Peter is somewhere to the right of Eric.
    problem.addConstraint(lambda p, e: p > e, ("pos_Peter", "pos_Eric"))

    # 2. The person who is short is in the first house.
    problem.addConstraint(lambda s: s == 1, (height_var_map["short"],))

    # 3. There is one house between the person who is short and the person who is very short.
    problem.addConstraint(
        lambda s, vs: abs(s - vs) == 2,
        (height_var_map["short"], height_var_map["very short"])
    )

    # 4. Arnold and the person who is very short are next to each other.
    problem.addConstraint(
        lambda a, vs: abs(a - vs) == 1,
        ("pos_Arnold", height_var_map["very short"])
    )

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    sol = solutions[0]

    # Build mappings from house to attributes
    house_to_name = {}
    for name in names:
        house_to_name[sol[f"pos_{name}"]] = name

    house_to_height = {}
    for h_label, var in height_var_map.items():
        house_to_height[sol[var]] = h_label

    # Prepare JSON output
    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": []
        }
    }

    for h in houses:
        result["solution"]["rows"].append([str(h), house_to_name[h], house_to_height[h]])

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()