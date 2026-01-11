import itertools
import json

def solve_puzzle():
    # Define the possible values for names and house styles
    names = ["Eric", "Arnold", "Alice", "Peter"]
    house_styles = ["craftsman", "colonial", "ranch", "victorian"]
    
    # Generate all possible permutations of names and house styles
    for name_permutation in itertools.permutations(names):
        for style_permutation in itertools.permutations(house_styles):
            # Create a list of houses with the current permutation
            houses = [
                {"house": 1, "name": name_permutation[0], "style": style_permutation[0]},
                {"house": 2, "name": name_permutation[1], "style": style_permutation[1]},
                {"house": 3, "name": name_permutation[2], "style": style_permutation[2]},
                {"house": 4, "name": name_permutation[3], "style": style_permutation[3]}
            ]
            
            # Check Clue 1: Alice is in the second house
            if houses[1]["name"] != "Alice":
                continue
            
            # Check Clue 5: The person in a Craftsman-style house is Alice
            if not any(house["name"] == "Alice" and house["style"] == "craftsman" for house in houses):
                continue
            
            # Check Clue 2: The person residing in a Victorian house is directly left of Peter
            for i in range(3):  # Only need to check up to the third house
                if houses[i]["style"] == "victorian" and houses[i + 1]["name"] == "Peter":
                    break
            else:
                continue
            
            # Check Clue 3: Peter is somewhere to the right of the person in a ranch-style home
            if not any(houses[i]["style"] == "ranch" and houses[j]["name"] == "Peter" for i in range(4) for j in range(i + 1, 4)):
                continue
            
            # Check Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house
            if not any(houses[i]["style"] == "craftsman" and houses[j]["name"] == "Arnold" for i in range(4) for j in range(i + 1, 4)):
                continue
            
            # If all constraints are satisfied, format the solution as JSON
            solution = {
                "solution": {
                    "header": ["House", "Name", "HouseStyle"],
                    "rows": [[str(house["house"]), house["name"], house["style"]] for house in houses]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())