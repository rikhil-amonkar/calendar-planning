import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    genres = ["science fiction", "romance", "mystery"]

    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for genre_perm in permutations(genres):
                # Assign attributes to houses
                assignment = []
                for i in range(3):
                    assignment.append({
                        "House": str(i + 1),
                        "Name": name_perm[i],
                        "smoothie": smoothie_perm[i],
                        "book genres": genre_perm[i]
                    })

                # Check all constraints
                # Constraint 5: Peter is in the first house
                if assignment[0]["Name"] != "Peter":
                    continue

                # Constraint 2: Arnold loves mystery books
                arnold_house = None
                mystery_house = None
                for house in assignment:
                    if house["Name"] == "Arnold":
                        arnold_house = house
                    if house["book genres"] == "mystery":
                        mystery_house = house
                if arnold_house != mystery_house:
                    continue

                # Constraint 1: Cherry smoothie is left of mystery books
                cherry_indices = [i for i, h in enumerate(assignment) if h["smoothie"] == "cherry"]
                mystery_index = next(i for i, h in enumerate(assignment) if h["book genres"] == "mystery" else -1
                if not all(i < mystery_index for i in cherry_indices):
                    continue

                # Constraint 4: Desert is directly left of mystery
                desert_left = False
                for i in range(2):
                    if assignment[i]["smoothie"] == "desert" and assignment[i+1]["book genres"] == "mystery":
                        desert_left = True
                        break
                if not desert_left:
                    continue

                # Constraint 3: Science fiction is not in the first house
                if assignment[0]["book genres"] == "science fiction":
                    continue

                # If all constraints are satisfied, prepare the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "smoothie", "book genres"],
                        "rows": [
                            [house["House"], house["Name"], house["smoothie"], house["book genres"]]
                            for house in assignment
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())