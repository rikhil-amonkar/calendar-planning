from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Eric', 'Peter', 'Alice', 'Arnold']
    cars = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    birthdays = ['jan', 'april', 'sept', 'feb']
    hobbies = ['painting', 'cooking', 'gardening', 'photography']
    houses = range(1, 5)

    # Create dictionaries to map variables to Z3 variables
    name_vars = {name: Int(f'name_{name}') for name in names}
    car_vars = {car: Int(f'car_{car}') for car in cars}
    birthday_vars = {birthday: Int(f'birthday_{birthday}') for birthday in birthdays}
    hobby_vars = {hobby: Int(f'hobby_{hobby}') for hobby in hobbies}

    # Create a solver instance
    solver = Solver()

    # Add constraints for unique assignment of houses
    solver.add(Distinct(name_vars.values()))
    solver.add(Distinct(car_vars.values()))
    solver.add(Distinct(birthday_vars.values()))
    solver.add(Distinct(hobby_vars.values()))

    # Ensure each variable is assigned a value between 1 and 4
    for var_dict in [name_vars, car_vars, birthday_vars, hobby_vars]:
        for var in var_dict.values():
            solver.add(And(var >= 1, var <= 4))

    # Add specific clues as constraints
    solver.add(name_vars['Peter'] == 1)  # Clue 11
    solver.add(birthday_vars['jan'] != 2)  # Clue 1
    solver.add(hobby_vars['photography'] < name_vars['Eric'])  # Clue 2
    solver.add(hobby_vars['photography'] < name_vars['Peter'])  # Clue 3
    solver.add(car_vars['honda civic'] + 1 == car_vars['tesla model 3'])  # Clue 4
    solver.add(Abs(car_vars['tesla model 3'] - hobby_vars['gardening']) == 2)  # Clue 5
    solver.add(name_vars['Arnold'] == car_vars['tesla model 3'])  # Clue 6
    solver.add(birthday_vars['feb'] == hobby_vars['cooking'])  # Clue 7
    solver.add(name_vars['Peter'] == car_vars['toyota camry'])  # Clue 8
    solver.add(birthday_vars['april'] == name_vars['Arnold'])  # Clue 9
    solver.add(hobby_vars['photography'] == name_vars['Alice'])  # Clue 10

    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in houses:
            name = next(name for name, var in name_vars.items() if model.evaluate(var) == house)
            car = next(car for car, var in car_vars.items() if model.evaluate(var) == house)
            birthday = next(birthday for birthday, var in birthday_vars.items() if model.evaluate(var) == house)
            hobby = next(hobby for hobby, var in hobby_vars.items() if model.evaluate(var) == house)
            solution.append([str(house), name, car, birthday, hobby])

        return {
            "solution": {
                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                "rows": solution
            }
        }
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))