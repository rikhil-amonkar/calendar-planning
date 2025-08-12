import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]
    
    # Initialize the possible combinations for each house
    house1 = {"name": None, "birthday": None, "color": None}
    house2 = {"name": None, "birthday": None, "color": None}
    
    # Apply the clues to deduce the solution
    
    # Clue 1: Eric is the person who loves yellow.
    # Clue 3: The person who loves yellow is not in the first house.
    # Therefore, Eric must be in the second house and loves yellow.
    house2["name"] = "Eric"
    house2["color"] = "yellow"
    
    # Since Eric is in the second house, Arnold must be in the first house.
    house1["name"] = "Arnold"
    
    # Clue 2: The person whose birthday is in April is in the first house.
    house1["birthday"] = "april"
    
    # Since the first house's birthday is April, the second house's birthday must be September.
    house2["birthday"] = "sept"
    
    # The only remaining color for the first house is red.
    house1["color"] = "red"
    
    # Construct the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": [
                ["1", house1["name"], house1["birthday"], house1["color"]],
                ["2", house2["name"], house2["birthday"], house2["color"]]
            ]
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

# Run the function to solve the puzzle and print the solution
solve_puzzle()