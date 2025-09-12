from z3 import *

def solve_puzzle():
    # Define domains
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    vacations = ["mountain", "city", "cruise", "beach", "camping"]
    educations = ["doctorate", "high school", "bachelor", "associate", "master"]
    colors = ["blue", "red", "white", "yellow", "green"]
    phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

    # Create variables
    name_vars = {name: Int(name) for name in names}
    vacation_vars = {vacation: Int(vacation) for vacation in vacations}
    education_vars = {education: Int(education) for education in educations}
    color_vars = {color: Int(color) for color in colors}
    phone_vars = {phone: Int(phone) for phone in phones}
    food_vars = {food: Int(food) for food in foods}

    # Solver instance
    solver = Solver()

    # Add constraints for each variable to be in the range of houses
    for var_dict in [name_vars, vacation_vars, education_vars, color_vars, phone_vars, food_vars]:
        for var in var_dict.values():
            solver.add(And(var >= 1, var <= 5))

    # All variables must be distinct
    solver.add(Distinct(list(name_vars.values())))
    solver.add(Distinct(list(vacation_vars.values())))
    solver.add(Distinct(list(education_vars.values())))
    solver.add(Distinct(list(color_vars.values())))
    solver.add(Distinct(list(phone_vars.values())))
    solver.add(Distinct(list(food_vars.values())))

    # Clue constraints
    solver.add(food_vars["stew"] != 1)
    solver.add(Abs(vacation_vars["city"] - education_vars["associate"]) == 3)  # Corrected key
    solver.add(vacation_vars["mountain"] == education_vars["bachelor"])
    solver.add(name_vars["Bob"] < education_vars["doctorate"])
    solver.add(phone_vars["samsung galaxy s21"] == 3)
    solver.add(name_vars["Eric"] == education_vars["doctorate"])
    solver.add(education_vars["doctorate"] == 3)
    solver.add(vacation_vars["beach"] == education_vars["bachelor"])  # Corrected key
    solver.add(education_vars["doctorate"] == food_vars["pizza"])
    solver.add(color_vars["green"] > name_vars["Peter"])
    solver.add(vacation_vars["camping"] == phone_vars["iphone 13"])
    solver.add(name_vars["Alice"] == vacation_vars["cruise"])
    solver.add(Abs(education_vars["high school"] - phone_vars["samsung galaxy s21"]) == 2)
    solver.add(phone_vars["google pixel 6"] == name_vars["Arnold"])
    solver.add(phone_vars["oneplus 9"] > phone_vars["huawei p50"])
    solver.add(name_vars["Arnold"] == food_vars["grilled cheese"])
    solver.add(food_vars["grilled cheese"] != 4)
    solver.add(Abs(education_vars["bachelor"] - color_vars["red"]) == 3)
    solver.add(vacation_vars["beach"] > vacation_vars["city"])
    solver.add(color_vars["green"] != 2)
    solver.add(color_vars["blue"] > name_vars["Peter"])
    solver.add(Abs(vacation_vars["camping"] - color_vars["yellow"]) == 2)

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in houses:
            house_solution = [str(house)]
            for var_dict in [name_vars, vacation_vars, education_vars, color_vars, phone_vars, food_vars]:
                for key, value in var_dict.items():
                    if model.evaluate(value) == house:
                        house_solution.append(key)
            solution.append(house_solution)
        return {
            "solution": {
                "header": ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"],
                "rows": solution
            }
        }
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))