from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the attributes
    names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
    phones = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

    # Create variables for each attribute in each house
    name_vars = {house: String(f"name_{house}") for house in houses}
    height_vars = {house: String(f"height_{house}") for house in houses}
    phone_vars = {house: String(f"phone_{house}") for house in houses}

    # Add constraints for uniqueness of each attribute
    s.add(Distinct([name_vars[house] for house in houses]))
    s.add(Distinct([height_vars[house] for house in houses]))
    s.add(Distinct([phone_vars[house] for house in houses]))

    # Each attribute must be one of the allowed values
    for house in houses:
        s.add(Or([name_vars[house] == name for name in names]))
        s.add(Or([height_vars[house] == height for height in heights]))
        s.add(Or([phone_vars[house] == phone for phone in phones]))

    # Add constraints based on the clues
    # Clue 1: Bob is directly left of the person who is tall.
    for i in range(1, 6):
        s.add(Implies(name_vars[i] == "Bob", And(height_vars[i+1] == "tall", name_vars[i+1] != "Bob")))

    # Clue 2: Peter is somewhere to the left of the person who uses an iPhone 13.
    for i in range(1, 6):
        for j in range(i+1, 7):
            s.add(Implies(And(name_vars[i] == "Peter", phone_vars[j] == "iphone 13"), True))

    # Clue 3: The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
    for i in range(1, 6):
        for j in range(i+1, 7):
            s.add(Implies(And(phone_vars[i] == "google pixel 6", height_vars[j] == "very short"), True))

    # Clue 4: Carol is the person who is very tall.
    for house in houses:
        s.add(Implies(name_vars[house] == "Carol", height_vars[house] == "very tall"))

    # Clue 5: There is one house between the person who uses a Google Pixel 6 and the person who is short.
    for i in range(1, 5):
        s.add(Implies(phone_vars[i] == "google pixel 6", height_vars[i+2] == "short"))

    # Clue 6: The person who uses a Samsung Galaxy S21 is not in the first house.
    s.add(phone_vars[1] != "samsung galaxy s21")

    # Clue 7: The person who uses a OnePlus 9 is directly left of the person who is short.
    for i in range(1, 6):
        s.add(Implies(phone_vars[i] == "oneplus 9", height_vars[i+1] == "short"))

    # Clue 8: The person who is tall is Arnold.
    for house in houses:
        s.add(Implies(height_vars[house] == "tall", name_vars[house] == "Arnold"))

    # Clue 9: The person who is super tall is in the first house.
    s.add(height_vars[1] == "super tall")

    # Clue 10: The person who uses a Xiaomi Mi 11 is Carol.
    for house in houses:
        s.add(Implies(phone_vars[house] == "xiaomi mi 11", name_vars[house] == "Carol"))

    # Clue 11: The person who uses a Google Pixel 6 is somewhere to the right of Eric.
    for i in range(2, 7):
        for j in range(1, i):
            s.add(Implies(And(name_vars[j] == "Eric", phone_vars[i] == "google pixel 6"), True))

    # Clue 12: The person who is short is in the sixth house.
    s.add(height_vars[6] == "short")

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Height", "PhoneModel"],
                "rows": []
            }
        }
        for house in houses:
            name = model.eval(name_vars[house])
            height = model.eval(height_vars[house])
            phone = model.eval(phone_vars[house])
            solution["solution"]["rows"].append([str(house), str(name), str(height), str(phone)])
        return solution
    else:
        return {"solution": {"header": ["House", "Name", "Height", "PhoneModel"], "rows": []}}

# Print the solution in JSON format
import json
print(json.dumps(solve_scheduling_problem(), indent=2))