import json

# Define the constraints and initial data
names = ["Eric", "Peter", "Arnold"]
mothers = ["Holly", "Aniya", "Janelle"]
foods = ["pizza", "grilled cheese", "spaghetti"]

# Initialize the solution grid
solution_grid = [[""] * 4 for _ in range(3)]

# Apply the clues to fill the grid
# Clue 4: Peter is the person whose mother's name is Holly.
# Clue 3: The person who loves eating grilled cheese is Eric.
# Clue 2: The person who loves eating grilled cheese is directly left of the person whose mother's name is Aniya.
# Clue 1: The person who loves the spaghetti eater and Peter are next to each other.

# Based on the deductions, we have:
solution_grid[0] = ["1", "Eric", "Janelle", "grilled cheese"]
solution_grid[1] = ["2", "Peter", "Holly", "pizza"]  # Pizza is the only food left for Peter
solution_grid[2] = ["3", "Arnold", "Aniya", "spaghetti"]

# Prepare the output in the required JSON format
output = {
    "solution": {
        "header": ["House", "Name", "Mother", "Food"],
        "rows": solution_grid
    }
}

# Convert to JSON and print
print(json.dumps(output, indent=2))