import json

def is_valid(state, constraints):
    # Check all constraints given the current state
    for constraint in constraints:
        if not constraint(state):
            return False
    return True

def solve_puzzle(constraints):
    # Possible values for each attribute
    people = ["Peter", "Arnold", "Eric"]
    cars = ["toyota camry", "ford f150", "tesla model 3"]
    styles = ["ranch", "colonial", "victorian"]
    pets = ["cat", "dog", "fish"]
    jobs = ["engineer", "doctor", "teacher"]
    vacations = ["city", "mountain", "beach"]

    # Initialize the state with empty values
    state = [{"name": None, "car": None, "style": None, "pet": None, "job": None, "vacation": None} for _ in range(3)]

    def backtrack(house_index, attribute_index):
        if house_index == 3:
            # All houses are filled, check if the solution is valid
            return is_valid(state, constraints)

        if attribute_index == 6:
            # All attributes for the current house are filled, move to the next house
            return backtrack(house_index + 1, 0)

        # Try each possible value for the current attribute
        if state[house_index][list(state[house_index].keys())[attribute_index]] is None:
            possible_values = []
            if list(state[house_index].keys())[attribute_index] == "name":
                possible_values = people
            elif list(state[house_index].keys())[attribute_index] == "car":
                possible_values = cars
            elif list(state[house_index].keys())[attribute_index] == "style":
                possible_values = styles
            elif list(state[house_index].keys())[attribute_index] == "pet":
                possible_values = pets
            elif list(state[house_index].keys())[attribute_index] == "job":
                possible_values = jobs
            elif list(state[house_index].keys())[attribute_index] == "vacation":
                possible_values = vacations

            for value in possible_values:
                if value not in [state[h][list(state[house_index].keys())[attribute_index]] for h in range(3) if h != house_index]:
                    state[house_index][list(state[house_index].keys())[attribute_index]] = value
                    if is_valid(state, constraints) and backtrack(house_index, attribute_index + 1):
                        return True
                    state[house_index][list(state[house_index].keys())[attribute_index]] = None

        else:
            # Move to the next attribute
            if backtrack(house_index, attribute_index + 1):
                return True

        return False

    if backtrack(0, 0):
        return state
    else:
        return None

# Define constraints as functions
constraints = [
    lambda s: s[0]["pet"] == "fish",  # Clue 1
    lambda s: s[1]["car"] == "toyota camry",  # Clue 2
    lambda s: s[1]["vacation"] != "mountain",  # Clue 3
    lambda s: s[1]["vacation"] != "city",  # Clue 4
    lambda s: (s[0]["name"] == "Peter" or s[0]["style"] == "ranch") and (s[1]["name"] != "Peter" or s[1]["style"] != "ranch"),  # Clue 5
    lambda s: s[1]["car"] == "toyota camry" and s[2]["style"] == "colonial",  # Clue 6
    lambda s: any(s[i]["name"] == "Arnold" and s[i]["pet"] == "cat" for i in range(3)),  # Clue 7
    lambda s: (s[0]["name"] == "Eric" or s[0]["vacation"] == "mountain") and (s[1]["name"] == "Eric" or s[1]["vacation"] == "mountain"),  # Clue 8
    lambda s: s[2]["job"] != "engineer",  # Clue 9
    lambda s: (s[0]["car"] == "tesla model 3" or s[0]["job"] == "teacher") and (s[1]["car"] == "tesla model 3" or s[1]["job"] == "teacher"),  # Clue 10
    lambda s: any(s[i]["pet"] == "dog" and s[i]["job"] == "engineer" for i in range(3))  # Clue 11
]

# Solve the puzzle
solution = solve_puzzle(constraints)

# Format the solution as JSON
if solution:
    formatted_solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": [
                [str(i+1), solution[i]["name"], solution[i]["car"], solution[i]["style"], solution[i]["pet"], solution[i]["job"], solution[i]["vacation"]]
                for i in range(3)
            ]
        }
    }
    print(json.dumps(formatted_solution, indent=2))
else:
    print("No solution found")