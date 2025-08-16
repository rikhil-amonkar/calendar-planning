from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]

    # Define the attributes
    names = ["Eric", "Peter", "Alice", "Arnold"]
    car_models = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
    birthday_months = ["jan", "april", "sept", "feb"]  # Note: "april" is misspelled as "april" in the problem statement, but clue 9 uses "april"
    hobbies = ["painting", "cooking", "gardening", "photography"]

    # Create variables for each attribute in each house
    name = {house: Int(f"name_{house}") for house in houses}
    car_model = {house: Int(f"car_model_{house}") for house in houses}
    birthday = {house: Int(f"birthday_{house}") for house in houses}
    hobby = {house: Int(f"hobby_{house}") for house in houses}

    # Add constraints to ensure each attribute is unique within its category
    for attr in [name, car_model, birthday, hobby]:
        s.add(Distinct([attr[house] for house in houses]))

    # Map the integer values to their corresponding strings
    name_map = {i: names[i] for i in range(len(names))}
    car_model_map = {i: car_models[i] for i in range(len(car_models))}
    birthday_map = {i: birthday_months[i] for i in range(len(birthday_months))}
    hobby_map = {i: hobbies[i] for i in range(len(hobbies))}

    # Ensure all variables are within the valid range
    for house in houses:
        s.add(name[house] >= 0, name[house] < len(names))
        s.add(car_model[house] >= 0, car_model[house] < len(car_models))
        s.add(birthday[house] >= 0, birthday[house] < len(birthday_months))
        s.add(hobby[house] >= 0, hobby[house] < len(hobbies))

    # Add constraints based on the clues
    # Clue 1: The person whose birthday is in jan is not in the second house.
    jan_index = birthday_months.index("jan")
    s.add(birthday[2] != jan_index)

    # Clue 2: The photography enthusiast is somewhere to the left of Eric.
    photography_index = hobbies.index("photography")
    eric_index = names.index("Eric")
    s.add(Or([And(hobby[house] == photography_index, name[house] != eric_index,
                  Or([name[h] == eric_index for h in houses if h > house])) for house in houses]))

    # Clue 3: The photography enthusiast is somewhere to the left of Peter.
    peter_index = names.index("Peter")
    s.add(Or([And(hobby[house] == photography_index, name[house] != peter_index,
                  Or([name[h] == peter_index for h in houses if h > house])) for house in houses]))

    # Clue 4: The person who owns a honda civic is directly left of the person who owns a tesla model 3.
    honda_index = car_models.index("honda civic")
    tesla_index = car_models.index("tesla model 3")
    s.add(Or([And(car_model[house] == honda_index, car_model[house + 1] == tesla_index) for house in [1, 2, 3]]))

    # Clue 5: There is one house between the person who owns a tesla model 3 and the person who enjoys gardening.
    gardening_index = hobbies.index("gardening")
    s.add(Or(
        And(car_model[1] == tesla_index, hobby[3] == gardening_index),
        And(car_model[2] == tesla_index, hobby[4] == gardening_index)
    ))

    # Clue 6: The person who owns a tesla model 3 is Arnold.
    arnold_index = names.index("Arnold")
    s.add(Or([And(car_model[house] == tesla_index, name[house] == arnold_index) for house in houses]))

    # Clue 7: The person whose birthday is in feb is the person who loves cooking.
    feb_index = birthday_months.index("feb")
    cooking_index = hobbies.index("cooking")
    s.add(Or([And(birthday[house] == feb_index, hobby[house] == cooking_index) for house in houses]))

    # Clue 8: The person who owns a toyota camry is Peter.
    toyota_index = car_models.index("toyota camry")
    s.add(Or([And(car_model[house] == toyota_index, name[house] == peter_index) for house in houses]))

    # Clue 9: The person whose birthday is in april is Arnold.
    april_index = birthday_months.index("april")
    s.add(Or([And(birthday[house] == april_index, name[house] == arnold_index) for house in houses]))

    # Clue 10: Alice is the photography enthusiast.
    alice_index = names.index("Alice")
    s.add(Or([And(name[house] == alice_index, hobby[house] == photography_index) for house in houses]))

    # Clue 11: Peter is the person whose birthday is in jan.
    s.add(Or([And(name[house] == peter_index, birthday[house] == jan_index) for house in houses]))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                "rows": []
            }
        }
        for house in houses:
            row = [
                str(house),
                name_map[model.evaluate(name[house]).as_long()],
                car_model_map[model.evaluate(car_model[house]).as_long()],
                birthday_map[model.evaluate(birthday[house]).as_long()],
                hobby_map[model.evaluate(hobby[house]).as_long()]
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"error": "No solution found"}

# Print the solution in JSON format
import json
print(json.dumps(solve_scheduling_problem(), indent=2))