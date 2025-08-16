import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]
    
    # Generate all possible permutations for the houses
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(colors))
    
    # Filter permutations based on the given clues
    valid_solutions = []
    for perm in all_permutations:
        name_perm, birthday_perm, color_perm = perm[0], perm[1], perm[2]
        
        # Unpack the permutations
        house1_name, house2_name = name_perm
        house1_birthday, house2_birthday = birthday_perm
        house1_color, house2_color = color_perm
        
        # Check clue 1: Eric is the person who loves yellow.
        if (house1_name == "Eric" and house1_color == "yellow") or \
           (house2_name == "Eric" and house2_color == "yellow"):
            continue
        
        # Check clue 2: The person whose birthday is in April is in the first house.
        if house1_birthday != "april":
            continue
        
        # Check clue 3: The person who loves yellow is not in the first house.
        if house1_color == "yellow":
            continue
        
        # If all clues are satisfied, add to valid solutions
        valid_solutions.append({
            "House": "1",
            "Name": house1_name,
            "Birthday": house1_birthday,
            "Color": house1_color
        }, {
            "House": "2",
            "Name": house2_name,
            "Birthday": house2_birthday,
            "Color": house2_color
        })
    
    # Format the solution as required
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": valid_solutions
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

solve_puzzle()