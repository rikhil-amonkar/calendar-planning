import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    children = ["Bella", "Fred"]
    lunches = ["grilled cheese", "pizza"]
    
    # Initialize the solution grid
    solution_grid = [
        {"House": "1", "Name": None, "Child": None, "Lunch": None},
        {"House": "2", "Name": None, "Child": None, "Lunch": None}
    ]
    
    # Apply the clues
    # Clue 1: The person who is a pizza lover is Arnold.
    for house in solution_grid:
        if house["Name"] == "Arnold":
            house["Lunch"] = "pizza"
        elif house["Lunch"] == "pizza":
            house["Name"] = "Arnold"
    
    # Clue 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
    for i in range(len(solution_grid) - 1):
        if solution_grid[i]["Lunch"] == "grilled cheese" or solution_grid[i]["Child"] == "Fred":
            solution_grid[i]["Lunch"] = "grilled cheese"
            solution_grid[i + 1]["Child"] = "Fred"
    
    # Fill in the remaining values
    for i in range(len(solution_grid)):
        if solution_grid[i]["Name"] is None:
            solution_grid[i]["Name"] = [name for name in names if name != solution_grid[1 - i]["Name"]][0]
        if solution_grid[i]["Child"] is None:
            solution_grid[i]["Child"] = [child for child in children if child != solution_grid[1 - i]["Child"]][0]
        if solution_grid[i]["Lunch"] is None:
            solution_grid[i]["Lunch"] = [lunch for lunch in lunches if lunch != solution_grid[1 - i]["Lunch"]][0]
    
    # Prepare the output in the required format
    output = {
        "solution": {
            "header": ["House", "Name", "Child", "Lunch"],
            "rows": [
                [house["House"], house["Name"], house["Child"], house["Lunch"]] for house in solution_grid
            ]
        }
    }
    
    return json.dumps(output, indent=2)

# Execute the function and print the result
print(solve_puzzle())