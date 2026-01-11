import json

# Define the houses, names, foods, and mothers
houses = [1, 2]
names = ['Arnold', 'Eric']
foods = ['grilled cheese', 'pizza']
mothers = ['Holly', 'Aniya']

# Initialize a dictionary to hold the solution
solution = {
    "solution": {
        "header": ["House", "Name", "Food", "Mother"],
        "rows": []
    }
}

# Apply the clues to determine the solution
house1_name = 'Arnold'  # From Clue 2 and Clue 3
house1_food = 'grilled cheese'  # From Clue 1
house1_mother = 'Holly'  # From Clue 3

house2_name = 'Eric'  # Only remaining name
house2_food = 'pizza'  # From Clue 1
house2_mother = 'Aniya'  # Only remaining mother

# Add the rows to the solution
solution["solution"]["rows"].append([str(houses[0]), house1_name, house1_food, house1_mother])
solution["solution"]["rows"].append([str(houses[1]), house2_name, house2_food, house2_mother])

# Convert the solution to a JSON string
json_solution = json.dumps(solution, indent=2)

# Print the JSON solution
print(json_solution)