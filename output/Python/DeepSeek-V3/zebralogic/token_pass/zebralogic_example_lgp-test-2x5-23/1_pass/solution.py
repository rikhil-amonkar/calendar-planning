import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]
    
    houses = [1, 2]
    
    # Generate all possible permutations for each attribute across houses
    # Since there are 2 houses, each permutation is a complete assignment
    all_solutions = []
    
    # Brute force search through all possible assignments
    for name_perm in permutations(names, 2):
        for edu_perm in permutations(educations, 2):
            for height_perm in permutations(heights, 2):
                for food_perm in permutations(foods, 2):
                    for drink_perm in permutations(drinks, 2):
                        # Create assignment for each house
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                "Name": name_perm[i],
                                "Education": edu_perm[i],
                                "Height": height_perm[i],
                                "Food": food_perm[i],
                                "Drink": drink_perm[i]
                            }
                        
                        # Check all clues
                        # Clue 1: The person who is very short is the person who is a pizza lover.
                        clue1 = True
                        for house in houses:
                            if assignment[house]["Height"] == "very short":
                                if assignment[house]["Food"] != "pizza":
                                    clue1 = False
                                    break
                            if assignment[house]["Food"] == "pizza":
                                if assignment[house]["Height"] != "very short":
                                    clue1 = False
                                    break
                        if not clue1:
                            continue
                        
                        # Clue 2: The person who loves eating grilled cheese is in the second house.
                        clue2 = (assignment[2]["Food"] == "grilled cheese")
                        if not clue2:
                            continue
                        
                        # Clue 3: The person with a high school diploma is the person who is a pizza lover.
                        clue3 = True
                        for house in houses:
                            if assignment[house]["Education"] == "high school":
                                if assignment[house]["Food"] != "pizza":
                                    clue3 = False
                                    break
                            if assignment[house]["Food"] == "pizza":
                                if assignment[house]["Education"] != "high school":
                                    clue3 = False
                                    break
                        if not clue3:
                            continue
                        
                        # Clue 4: The tea drinker is the person who loves eating grilled cheese.
                        clue4 = True
                        for house in houses:
                            if assignment[house]["Drink"] == "tea":
                                if assignment[house]["Food"] != "grilled cheese":
                                    clue4 = False
                                    break
                            if assignment[house]["Food"] == "grilled cheese":
                                if assignment[house]["Drink"] != "tea":
                                    clue4 = False
                                    break
                        if not clue4:
                            continue
                        
                        # Clue 5: Arnold is the person who is a pizza lover.
                        clue5 = True
                        for house in houses:
                            if assignment[house]["Name"] == "Arnold":
                                if assignment[house]["Food"] != "pizza":
                                    clue5 = False
                                    break
                            if assignment[house]["Food"] == "pizza":
                                if assignment[house]["Name"] != "Arnold":
                                    clue5 = False
                                    break
                        if not clue5:
                            continue
                        
                        # All clues satisfied, add to solutions
                        all_solutions.append(assignment)
    
    # We should have exactly one solution
    if len(all_solutions) == 0:
        raise ValueError("No solution found")
    
    # Take the first solution (should be only one)
    solution = all_solutions[0]
    
    # Format the output as required
    header = ["House", "Name", "Education", "Height", "Food", "Drink"]
    rows = []
    
    for house in sorted(solution.keys()):
        row = [
            str(house),
            solution[house]["Name"],
            solution[house]["Education"],
            solution[house]["Height"],
            solution[house]["Food"],
            solution[house]["Drink"]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    return json.dumps(result, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())