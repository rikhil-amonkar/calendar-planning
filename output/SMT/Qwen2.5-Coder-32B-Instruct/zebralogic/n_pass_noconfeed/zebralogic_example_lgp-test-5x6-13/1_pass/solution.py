from z3 import *

def solve_puzzle():
    # Define variables
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    foods = ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza']
    cars = ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic']
    phones = ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50']
    occupations = ['teacher', 'lawyer', 'doctor', 'artist', 'engineer']
    drinks = ['tea', 'milk', 'water', 'root beer', 'coffee']

    # Create variables for each house
    house_vars = [Int(f'house_{i}') for i in range(1, 6)]

    # Create dictionaries for each attribute
    name_vars = {name: Int(name) for name in names}
    food_vars = {food: Int(food) for food in foods}
    car_vars = {car: Int(car) for car in cars}
    phone_vars = {phone: Int(phone) for phone in phones}
    occupation_vars = {occupation: Int(occupation) for occupation in occupations}
    drink_vars = {drink: Int(drink) for drink in drinks}

    # Create solver instance
    solver = Solver()

    # Add constraints for each attribute to be in a house from 1 to 5
    for var_dict in [name_vars, food_vars, car_vars, phone_vars, occupation_vars, drink_vars]:
        solver.add(Distinct(*var_dict.values()))
        for var in var_dict.values():
            solver.add(var >= 1)
            solver.add(var <= 5)

    # Add specific clues as constraints
    solver.add(drink_vars['root beer'] == car_vars['honda civic'])
    solver.add(drink_vars['milk'] + 1 == food_vars['grilled cheese'])
    solver.add(phone_vars['samsung galaxy s21'] == name_vars['Alice'])
    solver.add(food_vars['stir fry'] == name_vars['Alice'])
    solver.add(drink_vars['tea'] != 5)
    solver.add(car_vars['bmw 3 series'] < drink_vars['tea'])
    solver.add(occupation_vars['doctor'] == name_vars['Arnold'])
    solver.add(phone_vars['iphone 13'] == drink_vars['coffee'])
    solver.add(occupation_vars['engineer'] == car_vars['bmw 3 series'])
    solver.add(food_vars['stew'] == phone_vars['iphone 13'])
    solver.add(occupation_vars['doctor'] + 1 == phone_vars['oneplus 9'])
    solver.add(car_vars['honda civic'] + 1 == food_vars['spaghetti'])
    solver.add(phone_vars['google pixel 6'] == drink_vars['tea'])
    solver.add(occupation_vars['artist'] == name_vars['Alice'])
    solver.add(Abs(name_vars['Alice'] - car_vars['ford f150']) == 2)
    solver.add(car_vars['toyota camry'] == name_vars['Arnold'])
    solver.add(name_vars['Eric'] == 4)
    solver.add(phone_vars['oneplus 9'] == occupation_vars['lawyer'])
    solver.add(food_vars['grilled cheese'] == name_vars['Peter'])

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in range(1, 6):
            house_solution = [str(house)]
            for var_dict in [name_vars, food_vars, car_vars, phone_vars, occupation_vars, drink_vars]:
                for key, value in var_dict.items():
                    if model.evaluate(value) == house:
                        house_solution.append(key)
            solution.append(house_solution)

        # Format the solution as JSON
        import json
        json_solution = {
            "solution": {
                "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                "rows": solution
            }
        }
        print(json.dumps(json_solution))
    else:
        print("No solution found")

solve_puzzle()