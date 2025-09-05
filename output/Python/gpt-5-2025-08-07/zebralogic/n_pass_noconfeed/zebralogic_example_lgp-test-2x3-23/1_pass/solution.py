import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2]  # Left to right
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]

    solutions = []

    # Generate all possible assignments (permutations ensure uniqueness)
    for name_assign in itertools.permutations(names, len(houses)):
        for child_assign in itertools.permutations(children, len(houses)):
            for food_assign in itertools.permutations(foods, len(houses)):
                # Constraint 1: The person who is a pizza lover is Arnold.
                try:
                    idx_pizza = food_assign.index("pizza")
                    idx_arnold = name_assign.index("Arnold")
                except ValueError:
                    continue
                if idx_pizza != idx_arnold:
                    continue

                # Constraint 2: The person who loves grilled cheese is directly left of the person whose child is Fred.
                try:
                    idx_grilled = food_assign.index("grilled cheese")
                    idx_fred = child_assign.index("Fred")
                except ValueError:
                    continue
                if not (idx_grilled + 1 == idx_fred):
                    continue

                # If all constraints satisfied, record solution
                assignment = []
                for i, house in enumerate(houses):
                    assignment.append({
                        "House": str(house),
                        "Name": name_assign[i],
                        "Children": child_assign[i],
                        "Food": food_assign[i],
                    })
                solutions.append(assignment)

    # Expect a unique solution for a well-posed puzzle
    if not solutions:
        raise ValueError("No solution found.")
    # If multiple, choose the first consistent solution
    sol = solutions[0]

    # Build JSON structure
    output = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": [[row["House"], row["Name"], row["Children"], row["Food"]] for row in sol]
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))