import json

def solve_puzzle():
    # Define the possible values
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]
    houses = [1, 2]

    # Initialize the solution list
    solutions = []

    # Try all permutations of names and vacations
    for i in range(len(names)):
        for j in range(len(vacations)):
            for k in range(len(names)):
                if k != i:  # Ensure different names for different houses
                    for l in range(len(vacations)):
                        if l != j:  # Ensure different vacations for different houses
                            # Apply the clue: Arnold is somewhere to the right of the person who loves beach vacations
                            if (names[i] == "Arnold" and vacations[j] == "beach") or \
                               (names[k] == "Arnold" and vacations[l] == "beach" and houses[k] > houses[i]) or \
                               (names[i] != "Arnold" and vacations[j] != "beach" and names[k] == "Arnold" and vacations[l] == "beach"):
                                # If the condition is satisfied, add the solution
                                solutions.append([["1", names[i], vacations[j]], ["2", names[k], vacations[l]]])

    # Output the first valid solution found
    if solutions:
        solution = solutions[0]
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": solution
            }
        }
        print(json.dumps(result, indent=2))

if __name__ == "__main__":
    solve_puzzle()