import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes and their possible values
    attributes = {
        "House": ["1", "2"],
        "Name": ["Eric", "Arnold"],
        "Favorite book genre": ["science fiction", "mystery"]
    }
    
    # Generate all possible permutations for each attribute
    name_perms = permutations(attributes["Name"])
    genre_perms = permutations(attributes["Favorite book genre"])
    
    # Iterate through all possible combinations
    for names in name_perms:
        for genres in genre_perms:
            # Assign values to houses
            solution = {
                "1": {
                    "House": "1",
                    "Name": names[0],
                    "Favorite book genre": genres[0]
                },
                "2": {
                    "House": "2",
                    "Name": names[1],
                    "Favorite book genre": genres[1]
                }
            }
            
            # Check the clues
            # Clue 1: Eric is directly left of the person who loves mystery books.
            # This means Eric is in house 1 and mystery is in house 2
            if solution["1"]["Name"] == "Eric" and solution["2"]["Favorite book genre"] == "mystery":
                # Format the solution as required
                output = {
                    "solution": {
                        "header": ["House", "Name", "Favorite book genre"],
                        "rows": [
                            [solution["1"]["House"], solution["1"]["Name"], solution["1"]["Favorite book genre"]],
                            [solution["2"]["House"], solution["2"]["Name"], solution["2"]["Favorite book genre"]]
                        ]
                    }
                }
                return output
    
    return {"solution": {}}

# Solve the puzzle and print the result as JSON
print(json.dumps(solve_puzzle(), indent=2))