import json
from itertools import permutations

def solve_puzzle():
    # Define possible values for each category
    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]
    houses = [1, 2]
    
    # Generate all permutations for each category
    name_perms = list(permutations(names, 2))
    food_perms = list(permutations(foods, 2))
    mother_perms = list(permutations(mothers, 2))
    
    solutions = []
    
    # Brute-force search over all combinations
    for name_assignment in name_perms:
        for food_assignment in food_perms:
            for mother_assignment in mother_perms:
                # Build the assignment dictionary
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        "Name": name_assignment[i],
                        "Food": food_assignment[i],
                        "Mother": mother_assignment[i]
                    }
                
                # Check clue 1: grilled cheese directly left of pizza
                # Since houses are 1 and 2, house 1 must be grilled cheese, house 2 must be pizza
                if not (assignment[1]["Food"] == "grilled cheese" and assignment[2]["Food"] == "pizza"):
                    continue
                
                # Check clue 2: Arnold is not in the second house
                if assignment[2]["Name"] == "Arnold":
                    continue
                
                # Check clue 3: Arnold's mother is Holly
                # Find Arnold's house
                arnold_house = None
                for house in houses:
                    if assignment[house]["Name"] == "Arnold":
                        arnold_house = house
                        break
                
                if arnold_house is None:
                    continue
                
                if assignment[arnold_house]["Mother"] != "Holly":
                    continue
                
                # All clues satisfied
                solutions.append(assignment)
    
    # We should have exactly one solution
    if len(solutions) != 1:
        raise ValueError(f"Expected 1 solution, found {len(solutions)}")
    
    solution = solutions[0]
    
    # Format the output as required
    rows = []
    for house in sorted(solution.keys()):
        row = [
            str(house),
            solution[house]["Name"],
            solution[house]["Food"],
            solution[house]["Mother"]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": rows
        }
    }
    
    return json.dumps(result, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())