import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]
    houses = [1, 2]

    # Initialize the solution list
    solutions = []

    # Iterate over all possible permutations of names and vacations
    for name1 in names:
        for name2 in names:
            if name1 != name2:
                for vacation1 in vacations:
                    for vacation2 in vacations:
                        if vacation1 != vacation2:
                            # Apply the clue: Arnold is somewhere to the right of the person who loves beach vacations.
                            if (name1 == "Arnold" and vacation2 == "beach") or (name2 == "Arnold" and vacation1 == "beach"):
                                # If the clue is satisfied, add the solution
                                solutions.append([["1", name1, vacation1], ["2", name2, vacation2]])

    # There should be only one valid solution, so we take the first one
    solution = solutions[0]

    # Format the solution as required JSON
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": solution
        }
    }

    # Print the JSON-formatted solution
    print(json.dumps(result))

# Run the function to solve the puzzle
solve_puzzle()