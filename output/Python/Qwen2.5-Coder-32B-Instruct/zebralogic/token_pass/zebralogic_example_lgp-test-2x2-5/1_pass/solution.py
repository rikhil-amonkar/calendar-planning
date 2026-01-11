import json

# Define the possible values
houses = ["1", "2"]
names = ["Eric", "Arnold"]
house_styles = ["victorian", "colonial"]

# Initialize the solution dictionary
solution_dict = {
    "solution": {
        "header": ["House", "Name", "HouseStyle"],
        "rows": []
    }
}

# According to Clue 2, Eric is in the first house
house_1_name = "Eric"
house_2_name = [name for name in names if name != house_1_name][0]  # Arnold

# According to Clue 1, the Victorian house must be to the left of the Colonial house
# Therefore, House 1 must be Victorian and House 2 must be Colonial
house_1_style = "victorian"
house_2_style = "colonial"

# Populate the rows with the deduced information
solution_dict["solution"]["rows"].append([houses[0], house_1_name, house_1_style])
solution_dict["solution"]["rows"].append([houses[1], house_2_name, house_2_style])

# Convert the solution dictionary to a JSON string
solution_json = json.dumps(solution_dict, indent=2)

# Print the JSON string
print(solution_json)