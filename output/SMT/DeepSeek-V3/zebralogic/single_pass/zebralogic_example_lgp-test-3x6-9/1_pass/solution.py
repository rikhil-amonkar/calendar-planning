from z3 import *

# Create the solver
s = Solver()

# Define the attributes for each house (1, 2, 3)
houses = [1, 2, 3]

# Define the possible values for each attribute
names = ["Peter", "Arnold", "Eric"]
car_models = ["toyota camry", "ford f150", "tesla model 3"]
house_styles = ["ranch", "colonial", "victorian"]
pets = ["cat", "dog", "fish"]
occupations = ["engineer", "doctor", "teacher"]
vacations = ["city", "mountain", "beach"]

# Create a dictionary to hold all the variables for each house
attributes = {
    "Name": {house: String(f"Name_{house}") for house in houses},
    "CarModel": {house: String(f"CarModel_{house}") for house in houses},
    "HouseStyle": {house: String(f"HouseStyle_{house}") for house in houses},
    "Pet": {house: String(f"Pet_{house}") for house in houses},
    "Occupation": {house: String(f"Occupation_{house}") for house in houses},
    "Vacation": {house: String(f"Vacation_{house}") for house in houses},
}

# Add constraints that all attributes within a category are distinct
for attr in ["Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"]:
    s.add(Distinct([attributes[attr][house] for house in houses]))

# Each attribute must be one of the allowed values
for house in houses:
    s.add(Or([attributes["Name"][house] == name for name in names]))
    s.add(Or([attributes["CarModel"][house] == car for car in car_models]))
    s.add(Or([attributes["HouseStyle"][house] == style for style in house_styles]))
    s.add(Or([attributes["Pet"][house] == pet for pet in pets]))
    s.add(Or([attributes["Occupation"][house] == occ for occ in occupations]))
    s.add(Or([attributes["Vacation"][house] == vac for vac in vacations]))

# Apply the clues one by one
# Clue 1: The person with an aquarium of fish is in the first house.
s.add(attributes["Pet"][1] == "fish")

# Clue 2: The person who owns a Toyota Camry is in the second house.
s.add(attributes["CarModel"][2] == "toyota camry")

# Clue 3: The person who enjoys mountain retreats is not in the second house.
s.add(attributes["Vacation"][2] != "mountain")

# Clue 4: The person who prefers city breaks is not in the second house.
s.add(attributes["Vacation"][2] != "city")

# Clue 5: The person in a ranch-style home is somewhere to the left of Peter.
# This means Peter is to the right of the ranch house.
# We model this by saying that the house with ranch is in a lower number than the house with Peter.
s.add(Or(
    And(attributes["HouseStyle"][1] == "ranch", Or(attributes["Name"][2] == "Peter", attributes["Name"][3] == "Peter")),
    And(attributes["HouseStyle"][2] == "ranch", attributes["Name"][3] == "Peter"),
))

# Clue 6: The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
# This means the house with toyota camry is immediately to the left of the colonial house.
s.add(Or(
    And(attributes["CarModel"][1] == "toyota camry", attributes["HouseStyle"][2] == "colonial"),
    And(attributes["CarModel"][2] == "toyota camry", attributes["HouseStyle"][3] == "colonial"),
))

# But from Clue 2, we know the toyota camry is in house 2, so:
s.add(attributes["HouseStyle"][3] == "colonial")

# Clue 7: Arnold is the person who has a cat.
for house in houses:
    s.add(Implies(attributes["Name"][house] == "Arnold", attributes["Pet"][house] == "cat"))

# Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
# This means the house with Eric has a lower number than the house with mountain vacation.
s.add(Or(
    And(attributes["Name"][1] == "Eric", Or(attributes["Vacation"][2] == "mountain", attributes["Vacation"][3] == "mountain")),
    And(attributes["Name"][2] == "Eric", attributes["Vacation"][3] == "mountain"),
))

# Clue 9: The person who is an engineer is not in the third house.
s.add(attributes["Occupation"][3] != "engineer")

# Clue 10: The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
# This means the tesla is in a house with a lower number than the teacher.
s.add(Or(
    And(attributes["CarModel"][1] == "tesla model 3", Or(attributes["Occupation"][2] == "teacher", attributes["Occupation"][3] == "teacher")),
    And(attributes["CarModel"][2] == "tesla model 3", attributes["Occupation"][3] == "teacher"),
))

# Clue 11: The person who owns a dog is the person who is an engineer.
for house in houses:
    s.add(Implies(attributes["Pet"][house] == "dog", attributes["Occupation"][house] == "engineer"))
    s.add(Implies(attributes["Occupation"][house] == "engineer", attributes["Pet"][house] == "dog"))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [str(house)]
        for attr in ["Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"]:
            # Get the value from the model
            value = model[attributes[attr][house]]
            # Convert to string and remove quotes if it's a string constant
            if is_string_value(value):
                value = value.as_string()
            else:
                value = str(value)
            row.append(value)
        solution["solution"]["rows"].append(row)
    
    # Print the solution as JSON
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")