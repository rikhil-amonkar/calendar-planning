import json
from itertools import permutations

def solve_puzzle():
    # Define the possible attributes
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    foods = ["grilled cheese", "pizza"]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for child_perm in permutations(children):
            for food_perm in permutations(foods):
                # Assign attributes to houses
                solution = []
                for i in range(2):
                    house = {
                        "House": str(i + 1),
                        "Name": name_perm[i],
                        "Children": child_perm[i],
                        "Food": food_perm[i]
                    }
                    solution.append(house)
                
                # Check the clues
                # Clue 1: The person who is a pizza lover is Arnold.
                clue1_passed = True
                for house in solution:
                    if house["Food"] == "pizza" and house["Name"] != "Arnold":
                        clue1_passed = False
                        break
                if not clue1_passed:
                    continue
                
                # Clue 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
                clue2_passed = False
                for i in range(1):
                    if solution[i]["Food"] == "grilled cheese" and solution[i + 1]["Children"] == "Fred":
                        clue2_passed = True
                        break
                if not clue2_passed:
                    continue
                
                # If all clues are passed, format the solution
                formatted_solution = {
                    "solution": {
                        "header": ["House", "Name", "Children", "Food"],
                        "rows": [
                            [solution[0]["House"], solution[0]["Name"], solution[0]["Children"], solution[0]["Food"]],
                            [solution[1]["House"], solution[1]["Name"], solution[1]["Children"], solution[1]["Food"]]
                        ]
                    }
                }
                return formatted_solution
    
    return {"solution": {"header": ["House", "Name", "Children", "Food"], "rows": []}}

# Solve the puzzle and print the result
result = solve_puzzle()
print(json.dumps(result, indent=2))