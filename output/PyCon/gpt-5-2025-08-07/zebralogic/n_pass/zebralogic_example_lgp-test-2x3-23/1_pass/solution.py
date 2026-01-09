import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2]

    # Attributes
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]

    # Create problem
    problem = Problem()

    # Variables: each attribute value maps to a house position
    for var in names + children + foods:
        problem.addVariable(var, houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), children)
    problem.addConstraint(AllDifferentConstraint(), foods)

    # Clue 1: The person who is a pizza lover is Arnold.
    problem.addConstraint(lambda pizza_pos, arnold_pos: pizza_pos == arnold_pos, ("pizza", "Arnold"))

    # Clue 2: The person who loves eating grilled cheese is directly left of the person whose child is named Fred.
    problem.addConstraint(lambda grilled_pos, fred_pos: grilled_pos == fred_pos - 1, ("grilled cheese", "Fred"))

    solutions = problem.getSolutions()
    if not solutions:
        # In case no solution is found (should not happen for this puzzle), output an empty structure
        output = {
            "solution": {
                "header": ["House", "Name", "Children", "Food"],
                "rows": [["1", "", "", ""], ["2", "", "", ""]]
            }
        }
        print(json.dumps(output))
        return

    sol = solutions[0]

    def value_at(category_list, house):
        for v in category_list:
            if sol[v] == house:
                return v
        return ""

    rows = []
    for h in houses:
        name = value_at(names, h)
        child = value_at(children, h)
        food = value_at(foods, h)
        rows.append([str(h), name, child, food])

    output = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()