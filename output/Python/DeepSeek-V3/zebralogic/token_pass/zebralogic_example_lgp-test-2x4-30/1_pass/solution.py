import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]
    
    houses = [1, 2]
    
    # Generate all possible permutations for each attribute across houses
    # Since there are 2 houses, each permutation is a complete assignment
    all_solutions = []
    
    # Brute force search through all possible assignments
    for name_perm in permutations(names, 2):
        for hair_perm in permutations(hair_colors, 2):
            for sport_perm in permutations(sports, 2):
                for smoothie_perm in permutations(smoothies, 2):
                    # Create assignment dictionary
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            "Name": name_perm[i],
                            "HairColor": hair_perm[i],
                            "FavoriteSport": sport_perm[i],
                            "Smoothie": smoothie_perm[i]
                        }
                    
                    # Check clue 1: The Desert smoothie lover is Arnold
                    clue1_ok = True
                    for house in houses:
                        if assignment[house]["Smoothie"] == "desert" and assignment[house]["Name"] != "Arnold":
                            clue1_ok = False
                            break
                        if assignment[house]["Name"] == "Arnold" and assignment[house]["Smoothie"] != "desert":
                            clue1_ok = False
                            break
                    if not clue1_ok:
                        continue
                    
                    # Check clue 2: The person who has brown hair is the person who loves basketball
                    clue2_ok = True
                    for house in houses:
                        if assignment[house]["HairColor"] == "brown" and assignment[house]["FavoriteSport"] != "basketball":
                            clue2_ok = False
                            break
                        if assignment[house]["FavoriteSport"] == "basketball" and assignment[house]["HairColor"] != "brown":
                            clue2_ok = False
                            break
                    if not clue2_ok:
                        continue
                    
                    # Check clue 3: Arnold is somewhere to the left of the person who has black hair
                    # Find Arnold's house
                    arnold_house = None
                    black_hair_house = None
                    for house in houses:
                        if assignment[house]["Name"] == "Arnold":
                            arnold_house = house
                        if assignment[house]["HairColor"] == "black":
                            black_hair_house = house
                    
                    if arnold_house is None or black_hair_house is None:
                        continue
                    
                    if not (arnold_house < black_hair_house):
                        continue
                    
                    # All clues satisfied, add to solutions
                    all_solutions.append(assignment)
    
    # There should be exactly one solution
    if len(all_solutions) != 1:
        raise ValueError(f"Expected 1 solution, found {len(all_solutions)}")
    
    solution = all_solutions[0]
    
    # Format the output as required
    rows = []
    for house in sorted(solution.keys()):
        row = [
            str(house),
            solution[house]["Name"],
            solution[house]["HairColor"],
            solution[house]["FavoriteSport"],
            solution[house]["Smoothie"]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": rows
        }
    }
    
    return json.dumps(result, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())