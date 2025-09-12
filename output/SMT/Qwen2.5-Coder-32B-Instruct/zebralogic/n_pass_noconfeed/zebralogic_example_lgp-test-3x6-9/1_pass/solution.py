from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Peter', 'Arnold', 'Eric']
    cars = ['toyota camry', 'ford f150', 'tesla model 3']
    styles = ['ranch', 'colonial', 'victorian']
    pets = ['cat', 'dog', 'fish']
    jobs = ['engineer', 'doctor', 'teacher']
    vacations = ['city', 'mountain', 'beach']

    # Create variables for each attribute in each house
    name_vars = [String(f'name_{i}') for i in range(1, 4)]
    car_vars = [String(f'car_{i}') for i in range(1, 4)]
    style_vars = [String(f'style_{i}') for i in range(1, 4)]
    pet_vars = [String(f'pet_{i}') for i in range(1, 4)]
    job_vars = [String(f'job_{i}') for i in range(1, 4)]
    vacation_vars = [String(f'vacation_{i}') for i in range(1, 4)]

    # Create a solver instance
    s = Solver()

    # Add domain constraints
    for i in range(3):
        s.add(name_vars[i] == Or(*[name for name in names]))
        s.add(car_vars[i] == Or(*[car for car in cars]))
        s.add(style_vars[i] == Or(*[style for style in styles]))
        s.add(pet_vars[i] == Or(*[pet for pet in pets]))
        s.add(job_vars[i] == Or(*[job for job in jobs]))
        s.add(vacation_vars[i] == Or(*[vacation for vacation in vacations]))

    # Add uniqueness constraints
    s.add(Distinct(name_vars))
    s.add(Distinct(car_vars))
    s.add(Distinct(style_vars))
    s.add(Distinct(pet_vars))
    s.add(Distinct(job_vars))
    s.add(Distinct(vacation_vars))

    # Add clue constraints
    s.add(pet_vars[0] == 'fish')  # Clue 1
    s.add(car_vars[1] == 'toyota camry')  # Clue 2
    s.add(vacation_vars[1] != 'mountain')  # Clue 3
    s.add(vacation_vars[1] != 'city')  # Clue 4
    s.add(Or(name_vars[0] == 'Peter', name_vars[1] == 'Peter'))  # Clue 5
    s.add(And(car_vars[1] == 'toyota camry', style_vars[2] == 'colonial'))  # Clue 6
    s.add(pet_vars[1] == 'cat')  # Clue 7
    s.add(Or(name_vars[0] == 'Eric', name_vars[1] == 'Eric'))  # Clue 8
    s.add(job_vars[2] != 'engineer')  # Clue 9
    s.add(Or(job_vars[0] == 'teacher', job_vars[1] == 'teacher'))  # Clue 10
    s.add(job_vars[2] == 'engineer')  # Clue 11
    s.add(pet_vars[2] == 'dog')  # Clue 11 (implied)

    # Check if the problem is solvable
    if s.check() == sat:
        m = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                "rows": []
            }
        }
        for i in range(1, 4):
            solution["solution"]["rows"].append([
                str(i),
                m[name_vars[i-1]].as_string()[1:-1],
                m[car_vars[i-1]].as_string()[1:-1],
                m[style_vars[i-1]].as_string()[1:-1],
                m[pet_vars[i-1]].as_string()[1:-1],
                m[job_vars[i-1]].as_string()[1:-1],
                m[vacation_vars[i-1]].as_string()[1:-1]
            ])
        return solution
    else:
        return None

# Solve the puzzle and print the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))