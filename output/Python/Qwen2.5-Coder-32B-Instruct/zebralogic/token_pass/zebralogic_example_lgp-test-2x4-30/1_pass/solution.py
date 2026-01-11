import itertools
import json

def solve_puzzle():
    # Define the variables
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    favorite_sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]
    
    # Generate all possible assignments for the two houses
    all_assignments = list(itertools.permutations(names)) * \
                      list(itertools.permutations(hair_colors)) * \
                      list(itertools.permutations(favorite_sports)) * \
                      list(itertools.permutations(smoothies))
    
    # Filter the assignments based on the constraints
    def is_valid(assignment):
        # Unpack the assignment into two houses
        house1, house2 = assignment
        
        # Unpack each house into its attributes
        name1, name2 = house1[0], house2[0]
        hair_color1, hair_color2 = house1[1], house2[1]
        favorite_sport1, favorite_sport2 = house1[2], house2[2]
        smoothie1, smoothie2 = house1[3], house2[3]
        
        # Apply the constraints
        if smoothie1 != "desert" or name1 != "Arnold":
            return False
        if hair_color1 == "black" or hair_color2 == "brown":
            return False
        if favorite_sport1 != "basketball" or hair_color1 != "brown":
            return False
        if favorite_sport2 != "soccer" or hair_color2 != "black":
            return False
        if name1 != "Arnold" or name2 != "Eric":
            return False
        
        return True
    
    # Find the valid assignment
    for assignment in all_assignments:
        # Convert the assignment into the required format
        house1 = [str(1)] + list(assignment[0])
        house2 = [str(2)] + list(assignment[1])
        
        if is_valid((house1, house2)):
            solution = {
                "solution": {
                    "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                    "rows": [house1, house2]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())