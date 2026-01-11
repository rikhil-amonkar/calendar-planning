import json

# Define the possible values
names = ["Arnold", "Eric"]
birthdays = ["april", "sept"]
mothers = ["Aniya", "Holly"]

# Initialize the solution structure
solution = {
    "solution": {
        "header": ["House", "Name", "Birthday", "Mother"],
        "rows": []
    }
}

# Based on logical deductions
house_1_name = "Eric"
house_1_birthday = "april"
house_1_mother = "Aniya"

house_2_name = "Arnold"
house_2_birthday = "sept"
house_2_mother = "Holly"

# Populate the rows with the solution
solution["solution"]["rows"].append(["1", house_1_name, house_1_birthday, house_1_mother])
solution["solution"]["rows"].append(["2", house_2_name, house_2_birthday, house_2_mother])

# Convert the solution to JSON format
json_solution = json.dumps(solution, indent=2)

# Print the JSON solution
print(json_solution)