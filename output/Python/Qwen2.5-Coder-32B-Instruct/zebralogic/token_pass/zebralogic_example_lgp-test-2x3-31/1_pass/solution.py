import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]
    
    # Initialize the houses with empty attributes
    houses = [{}, {}]
    
    # Apply the constraints
    # Constraint 1: Arnold enjoys gardening
    for i in range(2):
        if "Arnold" not in houses[i].values() and "gardening" not in houses[i].values():
            houses[i]["Name"] = "Arnold"
            houses[i]["Hobby"] = "gardening"
            break
    
    # Constraint 2: Photography enthusiast is not in the first house
    # Constraint 3: Soccer lover is not in the first house
    # Since Arnold is in the house with gardening, he cannot be in the first house if photography is there
    # Therefore, Eric must be in the first house with photography and basketball
    houses[0]["Name"] = "Eric"
    houses[0]["Hobby"] = "photography"
    houses[0]["FavoriteSport"] = "basketball"
    
    # By elimination, Arnold must be in the second house with soccer and gardening
    houses[1]["Name"] = "Arnold"
    houses[1]["FavoriteSport"] = "soccer"
    houses[1]["Hobby"] = "gardening"
    
    # Prepare the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": [
                ["1", houses[0]["Name"], houses[0]["FavoriteSport"], houses[0]["Hobby"]],
                ["2", houses[1]["Name"], houses[1]["FavoriteSport"], houses[1]["Hobby"]]
            ]
        }
    }
    
    return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())