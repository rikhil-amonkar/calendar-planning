import json
from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Define attributes
    names = ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter']
    birthdays = ['jan', 'feb', 'mar', 'april', 'may', 'sept']
    foods = ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    heights = ['very short', 'average', 'super tall', 'short', 'very tall', 'tall']
    car_models = ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']
    
    # Create variables for each attribute's house position
    name_vars = {n: Int(f'name_{n}') for n in names}
    birthday_vars = {b: Int(f'birthday_{b}') for b in birthdays}
    food_vars = {f: Int(f'food_{f.replace(" ", "_")}') for f in foods}
    height_vars = {h: Int(f'height_{h.replace(" ", "_")}') for h in heights}
    car_vars = {c: Int(f'car_{c.replace(" ", "_")}') for c in car_models}
    
    # All attributes must be in houses 1-6
    for var_dict in [name_vars, birthday_vars, food_vars, height_vars, car_vars]:
        for var in var_dict.values():
            solver.add(var >= 1, var <= 6)
    
    # All attributes within a category must be distinct
    solver.add(Distinct([v for v in name_vars.values()]))
    solver.add(Distinct([v for v in birthday_vars.values()]))
    solver.add(Distinct([v for v in food_vars.values()]))
    solver.add(Distinct([v for v in height_vars.values()]))
    solver.add(Distinct([v for v in car_vars.values()]))
    
    # Add constraints from clues
    solver.add(car_vars['honda civic'] == height_vars['short'])  # Clue 1
    solver.add(car_vars['ford f150'] == 5)  # Clue 2
    solver.add(food_vars['stir fry'] < name_vars['Eric'])  # Clue 3
    solver.add(birthday_vars['may'] < name_vars['Carol'])  # Clue 4
    solver.add(height_vars['very short'] < birthday_vars['april'])  # Clue 5
    solver.add(car_vars['bmw 3 series'] != 3)  # Clue 6
    solver.add(Abs(food_vars['stir fry'] - food_vars['pizza']) == 3)  # Clue 7
    solver.add(food_vars['soup'] + 1 == name_vars['Eric'])  # Clue 8
    solver.add(Abs(food_vars['spaghetti'] - birthday_vars['may']) == 1)  # Clue 9
    solver.add(name_vars['Alice'] + 1 == car_vars['bmw 3 series'])  # Clue 10
    solver.add(car_vars['tesla model 3'] < height_vars['tall'])  # Clue 11
    solver.add(height_vars['very tall'] == car_vars['toyota camry'])  # Clue 12
    solver.add(name_vars['Peter'] + 1 == food_vars['pizza'])  # Clue 13
    solver.add(food_vars['stew'] != 3)  # Clue 14
    solver.add(Abs(birthday_vars['sept'] - height_vars['very short']) == 2)  # Clue 15
    solver.add(Abs(birthday_vars['mar'] - height_vars['super tall']) == 2)  # Clue 16
    solver.add(height_vars['tall'] == name_vars['Bob'])  # Clue 17
    solver.add(birthday_vars['may'] > name_vars['Alice'])  # Clue 18
    solver.add(height_vars['very short'] == 4)  # Clue 19
    solver.add(birthday_vars['mar'] == height_vars['short'])  # Clue 20
    solver.add(name_vars['Carol'] == car_vars['tesla model 3'])  # Clue 21
    solver.add(name_vars['Eric'] == birthday_vars['jan'])  # Clue 22
    
    # Check satisfiability
    if solver.check() != sat:
        print("No solution found")
        return
        
    model = solver.model()
    
    # Create assignment dictionaries
    assignment = {}
    for house in range(1, 7):
        assignment[house] = {
            'Name': None,
            'Birthday': None,
            'Food': None,
            'Height': None,
            'CarModel': None
        }
    
    # Assign names
    for name, var in name_vars.items():
        house = model[var].as_long()
        assignment[house]['Name'] = name
        
    # Assign birthdays
    for bday, var in birthday_vars.items():
        house = model[var].as_long()
        assignment[house]['Birthday'] = bday
        
    # Assign foods
    for food, var in food_vars.items():
        house = model[var].as_long()
        assignment[house]['Food'] = food
        
    # Assign heights
    for height, var in height_vars.items():
        house = model[var].as_long()
        assignment[house]['Height'] = height
        
    # Assign car models
    for car, var in car_vars.items():
        house = model[var].as_long()
        assignment[house]['CarModel'] = car
        
    # Prepare JSON output
    header = ["House", "Name", "Birthday", "Food", "Height", "CarModel"]
    rows = []
    for house in range(1, 7):
        row = [
            str(house),
            assignment[house]['Name'],
            assignment[house]['Birthday'],
            assignment[house]['Food'],
            assignment[house]['Height'],
            assignment[house]['CarModel']
        ]
        rows.append(row)
    
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()