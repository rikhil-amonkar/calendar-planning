import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ["Eric", "Arnold"]
    lunches = ["pizza", "grilled cheese"]
    
    # Initialize the possible solutions
    solutions = []
    
    # Iterate over all permutations of names and lunches
    for name1 in names:
        for lunch1 in lunches:
            for name2 in names:
                if name2 != name1:  # Ensure different names for different houses
                    for lunch2 in lunches:
                        if lunch2 != lunch1:  # Ensure different lunches for different houses
                            # Apply the clues
                            if lunch2 == "pizza" and name2 != "Arnold":
                                solutions.append([["1", name1, lunch1], ["2", name2, lunch2]])
    
    # Convert the solution to the required JSON format
    if solutions:
        solution_json = {
            "solution": {
                "header": ["House", "Name", "Lunch"],
                "rows": solutions[0]
            }
        }
        print(json.dumps(solution_json, indent=2))
    else:
        print("No solution found")

# Run the function to solve the puzzle
solve_puzzle()