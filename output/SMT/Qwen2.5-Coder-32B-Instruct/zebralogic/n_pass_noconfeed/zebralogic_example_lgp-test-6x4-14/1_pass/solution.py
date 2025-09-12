from z3 import *

def solve_puzzle():
    # Define the domain for each attribute
    houses = [Int(f'house_{i}') for i in range(1, 7)]
    names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    cars = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']

    # Create Z3 variables for each attribute
    name_vars = {name: Int(name) for name in names}
    car_vars = {car: Int(car) for car in cars}
    mother_vars = {mother: Int(mother) for mother in mothers}
    hobby_vars = {hobby: Int(hobby) for hobby in hobbies}

    # Create a solver instance
    solver = Solver()

    # Add constraints for each attribute to be in the range 1 to 6
    for var_dict in [name_vars, car_vars, mother_vars, hobby_vars]:
        for var in var_dict.values():
            solver.add(And(var >= 1, var <= 6))

    # Add constraints for all attributes to be distinct
    solver.add(Distinct(list(name_vars.values())))
    solver.add(Distinct(list(car_vars.values())))
    solver.add(Distinct(list(mother_vars.values())))
    solver.add(Distinct(list(hobby_vars.values())))

    # Add specific clues as constraints
    solver.add(car_vars['toyota camry'] == 6)
    solver.add(hobby_vars['photography'] == name_vars['Carol'])
    solver.add(car_vars['chevrolet silverado'] == mother_vars['Aniya'])
    solver.add(car_vars['chevrolet silverado'] != 2)
    solver.add(car_vars['ford f150'] == mother_vars['Sarah'])
    solver.add(car_vars['bmw 3 series'] == name_vars['Bob'])
    solver.add(mother_vars['Kailyn'] == 6)
    solver.add(name_vars['Eric'] + 1 == hobby_vars['knitting'])
    solver.add(Abs(mother_vars['Sarah'] - car_vars['toyota camry']) == 1)
    solver.add(mother_vars['Penny'] > hobby_vars['knitting'])
    solver.add(mother_vars['Aniya'] > car_vars['honda civic'])
    solver.add(name_vars['Alice'] > car_vars['ford f150'])
    solver.add(hobby_vars['gardening'] == name_vars['Eric'])
    solver.add(hobby_vars['woodworking'] < hobby_vars['knitting'])
    solver.add(Abs(mother_vars['Sarah'] - hobby_vars['cooking']) == 1)
    solver.add(car_vars['honda civic'] == name_vars['Arnold'])
    solver.add(mother_vars['Holly'] + 1 == hobby_vars['knitting'])

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for house in range(1, 7):
            name = next(name for name, var in name_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
            car = next(car for car, var in car_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
            mother = next(mother for mother, var in mother_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
            hobby = next(hobby for hobby, var in hobby_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
            solution.append([str(house), name, car, mother, hobby])
        return {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": solution
            }
        }
    else:
        return None

# Solve the puzzle and print the solution in JSON format
import json
print(json.dumps(solve_puzzle(), indent=2))