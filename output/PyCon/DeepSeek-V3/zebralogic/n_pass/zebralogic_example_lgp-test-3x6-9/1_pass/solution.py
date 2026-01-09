import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house (1, 2, 3)
    houses = [1, 2, 3]
    
    # Define domains for each attribute
    names = ['Peter', 'Arnold', 'Eric']
    car_models = ['toyota camry', 'ford f150', 'tesla model 3']
    house_styles = ['ranch', 'colonial', 'victorian']
    pets = ['cat', 'dog', 'fish']
    occupations = ['engineer', 'doctor', 'teacher']
    vacations = ['city', 'mountain', 'beach']
    
    # Add variables for each attribute per house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'car_{house}', car_models)
        problem.addVariable(f'style_{house}', house_styles)
        problem.addVariable(f'pet_{house}', pets)
        problem.addVariable(f'occupation_{house}', occupations)
        problem.addVariable(f'vacation_{house}', vacations)
    
    # All attributes must be different within their category
    problem.addConstraint(lambda a, b, c: len({a, b, c}) == 3, 
                         [f'name_{h}' for h in houses])
    problem.addConstraint(lambda a, b, c: len({a, b, c}) == 3, 
                         [f'car_{h}' for h in houses])
    problem.addConstraint(lambda a, b, c: len({a, b, c}) == 3, 
                         [f'style_{h}' for h in houses])
    problem.addConstraint(lambda a, b, c: len({a, b, c}) == 3, 
                         [f'pet_{h}' for h in houses])
    problem.addConstraint(lambda a, b, c: len({a, b, c}) == 3, 
                         [f'occupation_{h}' for h in houses])
    problem.addConstraint(lambda a, b, c: len({a, b, c}) == 3, 
                         [f'vacation_{h}' for h in houses])
    
    # Clue 1: The person with an aquarium of fish is in the first house.
    problem.addConstraint(lambda pet: pet == 'fish', ['pet_1'])
    
    # Clue 2: The person who owns a Toyota Camry is in the second house.
    problem.addConstraint(lambda car: car == 'toyota camry', ['car_2'])
    
    # Clue 3: The person who enjoys mountain retreats is not in the second house.
    problem.addConstraint(lambda vac: vac != 'mountain', ['vacation_2'])
    
    # Clue 4: The person who prefers city breaks is not in the second house.
    problem.addConstraint(lambda vac: vac != 'city', ['vacation_2'])
    
    # Clue 5: The person in a ranch-style home is somewhere to the left of Peter.
    for i in houses:
        for j in houses:
            if j <= i:  # j is not to the left of i
                continue
            problem.addConstraint(
                lambda style, name, house_i=i, house_j=j: 
                not (style == 'ranch' and name == 'Peter' and house_i >= house_j),
                [f'style_{i}', f'name_{j}']
            )
    
    # Clue 6: The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
    problem.addConstraint(lambda style: style == 'colonial', ['style_3'])
    
    # Clue 7: Arnold is the person who has a cat.
    for house in houses:
        problem.addConstraint(
            lambda name, pet, h=house: not (name == 'Arnold' and pet != 'cat'),
            [f'name_{house}', f'pet_{house}']
        )
        problem.addConstraint(
            lambda name, pet, h=house: not (pet == 'cat' and name != 'Arnold'),
            [f'name_{house}', f'pet_{house}']
        )
    
    # Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
    for i in houses:
        for j in houses:
            if j <= i:  # j is not to the left of i
                continue
            problem.addConstraint(
                lambda name, vacation, house_i=i, house_j=j: 
                not (name == 'Eric' and vacation == 'mountain' and house_i >= house_j),
                [f'name_{i}', f'vacation_{j}']
            )
    
    # Clue 9: The person who is an engineer is not in the third house.
    problem.addConstraint(lambda occ: occ != 'engineer', ['occupation_3'])
    
    # Clue 10: The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
    for i in houses:
        for j in houses:
            if j <= i:  # j is not to the left of i
                continue
            problem.addConstraint(
                lambda car, occupation, house_i=i, house_j=j: 
                not (car == 'tesla model 3' and occupation == 'teacher' and house_i >= house_j),
                [f'car_{i}', f'occupation_{j}']
            )
    
    # Clue 11: The person who owns a dog is the person who is an engineer.
    for house in houses:
        problem.addConstraint(
            lambda pet, occupation, h=house: not (pet == 'dog' and occupation != 'engineer'),
            [f'pet_{house}', f'occupation_{house}']
        )
        problem.addConstraint(
            lambda pet, occupation, h=house: not (occupation == 'engineer' and pet != 'dog'),
            [f'pet_{house}', f'occupation_{house}']
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Prepare the output
    header = ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'car_{house}'],
            solution[f'style_{house}'],
            solution[f'pet_{house}'],
            solution[f'occupation_{house}'],
            solution[f'vacation_{house}']
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))