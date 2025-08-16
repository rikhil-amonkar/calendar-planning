import json
from itertools import permutations

def solve_puzzle():
    # Define the possible attributes
    names = ["Eric", "Arnold"]
    genres = ["science fiction", "mystery"]
    
    # Generate all possible permutations for names and genres
    for name_assignment in permutations(names):
        for genre_assignment in permutations(genres):
            # Check the constraints
            # Constraint 1: Eric is directly left of the person who loves mystery books
            # This means Eric must be in house 1 and mystery in house 2
            if name_assignment[0] == "Eric" and genre_assignment[1] == "mystery":
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre"],
                        "rows": [
                            ["1", name_assignment[0], genre_assignment[0]],
                            ["2", name_assignment[1], genre_assignment[1]]
                        ]
                    }
                }
                return json.dumps(solution)
    
    # If no solution found (though the puzzle should have one)
    return json.dumps({"solution": {"header": ["House", "Name", "BookGenre"], "rows": []}})

# Execute and print the solution
print(solve_puzzle())