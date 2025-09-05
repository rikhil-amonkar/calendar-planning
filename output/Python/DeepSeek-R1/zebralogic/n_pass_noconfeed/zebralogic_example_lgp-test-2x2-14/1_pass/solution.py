import json

def main():
    # Define the attributes
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]
    
    # Initialize assignments
    assignment = {
        1: {"Name": None, "Food": None},
        2: {"Name": None, "Food": None}
    }
    
    # Apply clue 1: Pizza is in house 2
    assignment[2]["Food"] = "pizza"
    # The remaining food must be in house 1
    assignment[1]["Food"] = next(food for food in foods if food != "pizza")
    
    # Apply clue 2: Arnold is not in house 1
    assignment[1]["Name"] = "Eric"  # Since only two houses, Eric must be in house 1
    assignment[2]["Name"] = "Arnold"
    
    # Prepare the output
    header = ["House", "Name", "Food"]
    rows = []
    for house in sorted(assignment.keys()):
        row = [str(house), assignment[house]["Name"], assignment[house]["Food"]]
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict, indent=2))

if __name__ == "__main__":
    main()