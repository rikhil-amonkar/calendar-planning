import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]
    
    # Generate all possible combinations
    all_combinations = list(itertools.permutations(names))
    all_combinations.extend(list(itertools.permutations(educations)))
    all_combinations.extend(list(itertools.permutations(heights)))
    all_combinations.extend(list(itertools.permutations(foods)))
    all_combinations.extend(list(itertools.permutations(drinks)))
    
    # Iterate over all possible assignments
    for name_perm in itertools.permutations(names):
        for education_perm in itertools.permutations(educations):
            for height_perm in itertools.permutations(heights):
                for food_perm in itertools.permutations(foods):
                    for drink_perm in itertools.permutations(drinks):
                        # Create a dictionary to store the assignment for each house
                        house1 = {
                            "Name": name_perm[0],
                            "Education": education_perm[0],
                            "Height": height_perm[0],
                            "Food": food_perm[0],
                            "Drink": drink_perm[0]
                        }
                        house2 = {
                            "Name": name_perm[1],
                            "Education": education_perm[1],
                            "Height": height_perm[1],
                            "Food": food_perm[1],
                            "Drink": drink_perm[1]
                        }
                        
                        # Check the clues
                        if (house1["Height"] == "very short" and house1["Food"] == "pizza" and
                            house2["Food"] == "grilled cheese" and
                            house1["Education"] == "high school" and house1["Food"] == "pizza" and
                            house2["Drink"] == "tea" and house2["Food"] == "grilled cheese" and
                            house1["Name"] == "Arnold" and house1["Food"] == "pizza"):
                            
                            # If all clues are satisfied, format the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                                    "rows": [
                                        ["1", house1["Name"], house1["Education"], house1["Height"], house1["Food"], house1["Drink"]],
                                        ["2", house2["Name"], house2["Education"], house2["Height"], house2["Food"], house2["Drink"]]
                                    ]
                                }
                            }
                            
                            # Output the solution as JSON
                            print(json.dumps(solution, indent=4))
                            return

# Run the solver
solve_puzzle()