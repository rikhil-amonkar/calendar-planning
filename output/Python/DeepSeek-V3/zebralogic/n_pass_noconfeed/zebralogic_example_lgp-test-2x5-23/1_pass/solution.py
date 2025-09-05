import json

def main():
    # Define the attributes and their possible values
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]
    
    # Since there are only 2 houses, we can use a brute force approach
    # Generate all possible combinations for each attribute
    from itertools import permutations
    
    # Generate all possible assignments for each attribute
    name_perms = list(permutations(names))
    education_perms = list(permutations(educations))
    height_perms = list(permutations(heights))
    food_perms = list(permutations(foods))
    drink_perms = list(permutations(drinks))
    
    # Try all possible combinations
    for name_assignment in name_perms:
        for education_assignment in education_perms:
            for height_assignment in height_perms:
                for food_assignment in food_perms:
                    for drink_assignment in drink_perms:
                        # Create the assignment for both houses
                        assignment = {
                            1: {
                                "Name": name_assignment[0],
                                "Education": education_assignment[0],
                                "Height": height_assignment[0],
                                "Food": food_assignment[0],
                                "Drink": drink_assignment[0]
                            },
                            2: {
                                "Name": name_assignment[1],
                                "Education": education_assignment[1],
                                "Height": height_assignment[1],
                                "Food": food_assignment[1],
                                "Drink": drink_assignment[1]
                            }
                        }
                        
                        # Check all clues
                        # Clue 1: The person who is very short is the person who is a pizza lover.
                        very_short_house = None
                        pizza_lover_house = None
                        for house, attrs in assignment.items():
                            if attrs["Height"] == "very short":
                                very_short_house = house
                            if attrs["Food"] == "pizza":
                                pizza_lover_house = house
                        if very_short_house != pizza_lover_house:
                            continue
                            
                        # Clue 2: The person who loves eating grilled cheese is in the second house.
                        grilled_cheese_house = None
                        for house, attrs in assignment.items():
                            if attrs["Food"] == "grilled cheese":
                                grilled_cheese_house = house
                        if grilled_cheese_house != 2:
                            continue
                            
                        # Clue 3: The person with a high school diploma is the person who is a pizza lover.
                        high_school_house = None
                        for house, attrs in assignment.items():
                            if attrs["Education"] == "high school":
                                high_school_house = house
                        if high_school_house != pizza_lover_house:
                            continue
                            
                        # Clue 4: The tea drinker is the person who loves eating grilled cheese.
                        tea_drinker_house = None
                        for house, attrs in assignment.items():
                            if attrs["Drink"] == "tea":
                                tea_drinker_house = house
                        if tea_drinker_house != grilled_cheese_house:
                            continue
                            
                        # Clue 5: Arnold is the person who is a pizza lover.
                        arnold_house = None
                        for house, attrs in assignment.items():
                            if attrs["Name"] == "Arnold":
                                arnold_house = house
                        if arnold_house != pizza_lover_house:
                            continue
                            
                        # If we get here, all clues are satisfied
                        # Format the solution as required
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                                "rows": [
                                    ["1", 
                                     assignment[1]["Name"],
                                     assignment[1]["Education"],
                                     assignment[1]["Height"],
                                     assignment[1]["Food"],
                                     assignment[1]["Drink"]],
                                    ["2",
                                     assignment[2]["Name"],
                                     assignment[2]["Education"],
                                     assignment[2]["Height"],
                                     assignment[2]["Food"],
                                     assignment[2]["Drink"]]
                                ]
                            }
                        }
                        
                        # Output the solution as JSON
                        print(json.dumps(solution, indent=2))
                        return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()