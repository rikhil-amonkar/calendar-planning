import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers_names = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]

    # Generate all possible permutations for each attribute
    permutations = list(itertools.permutations(names))
    permutations_mothers = list(itertools.permutations(mothers_names))
    permutations_flowers = list(itertools.permutations(flowers))

    # Iterate through all combinations of permutations
    for perm_name in permutations:
        for perm_mother in permutations_mothers:
            for perm_flower in permutations_flowers:
                # Create a list of dictionaries representing each house
                houses = []
                for i in range(4):
                    houses.append({
                        "House": str(i + 1),
                        "Name": perm_name[i],
                        "Mother's Name": perm_mother[i],
                        "Favorite Flower": perm_flower[i]
                    })

                # Check all the clues
                if (houses[2]["Name"] == "Alice" and  # Clue 8
                    houses[2]["Mother's Name"] == "Kailyn" and  # Clue 1
                    houses[0]["Mother's Name"] == "Holly" and  # Clue 5
                    houses[2]["Favorite Flower"] == "lilies" and  # Clue 7
                    houses[3]["Name"] == "Eric" and  # Clue 4
                    houses[3]["Favorite Flower"] == "daffodils" and  # Clue 4
                    houses.index(next(house for house in houses if house["Mother's Name"] == "Janelle")) >  # Clue 2
                    houses.index(next(house for house in houses if house["Name"] == "Arnold")) and
                    houses.index(next(house for house in houses if house["Mother's Name"] == "Holly")) <  # Clue 6
                    houses.index(next(house for house in houses if house["Favorite Flower"] == "carnations")) and
                    houses.index(next(house for house in houses if house["Name"] == "Peter")) >  # Clue 3
                    houses.index(next(house for house in houses if house["Favorite Flower"] == "carnations"))):
                    
                    # If all clues are satisfied, return the solution in JSON format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother's Name", "Favorite Flower"],
                            "rows": [
                                [house["House"], house["Name"], house["Mother's Name"], house["Favorite Flower"]]
                                for house in houses
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())