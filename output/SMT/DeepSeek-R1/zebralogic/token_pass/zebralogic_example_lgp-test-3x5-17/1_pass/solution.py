import json
from z3 import *

def main():
    # Create solver
    solver = Solver()

    # Define the attributes and their possible values
    names = ['Eric', 'Arnold', 'Peter']
    phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    heights = ['very short', 'average', 'short']
    house_styles = ['colonial', 'ranch', 'victorian']
    cars = ['tesla model 3', 'toyota camry', 'ford f150']

    # Create Z3 variables for each attribute in each house
    name_vars = [Int(f'name_{i}') for i in range(1,4)]
    phone_vars = [Int(f'phone_{i}') for i in range(1,4)]
    height_vars = [Int(f'height_{i}') for i in range(1,4)]
    style_vars = [Int(f'style_{i}') for i in range(1,4)]
    car_vars = [Int(f'car_{i}') for i in range(1,4)]

    # Constraint: All attributes must be between 0-2 (indices of possible values)
    for var in name_vars + phone_vars + height_vars + style_vars + car_vars:
        solver.add(var >= 0, var <= 2)

    # Constraint: All attributes within a category must be distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(phone_vars))
    solver.add(Distinct(height_vars))
    solver.add(Distinct(style_vars))
    solver.add(Distinct(car_vars))

    # Add clues constraints
    # 1. Peter is somewhere to the right of Eric.
    peter_index = names.index('Peter')
    eric_index = names.index('Eric')
    solver.add(Or(
        And(name_vars[0] == eric_index, name_vars[1] == peter_index),
        And(name_vars[0] == eric_index, name_vars[2] == peter_index),
        And(name_vars[1] == eric_index, name_vars[2] == peter_index)
    ))

    # 2. The person living in a colonial-style house is in the second house.
    colonial_index = house_styles.index('colonial')
    solver.add(style_vars[1] == colonial_index)

    # 3. The person who owns a Tesla Model 3 is the person who is very short.
    tesla_index = cars.index('tesla model 3')
    very_short_index = heights.index('very short')
    for i in range(3):
        solver.add(Implies(car_vars[i] == tesla_index, height_vars[i] == very_short_index))

    # 4. The person who is short is directly left of the person who uses a Samsung Galaxy S21.
    short_index = heights.index('short')
    samsung_index = phones.index('samsung galaxy s21')
    solver.add(Or(
        And(height_vars[0] == short_index, phone_vars[1] == samsung_index),
        And(height_vars[1] == short_index, phone_vars[2] == samsung_index)
    ))

    # 5. The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
    iphone_index = phones.index('iphone 13')
    pixel_index = phones.index('google pixel 6')
    solver.add(Or(
        And(phone_vars[0] == iphone_index, phone_vars[1] == pixel_index),
        And(phone_vars[1] == iphone_index, phone_vars[2] == pixel_index)
    ))

    # 6. The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
    ranch_index = house_styles.index('ranch')
    solver.add(Or(
        And(style_vars[0] == ranch_index, style_vars[1] == colonial_index),
        And(style_vars[0] == ranch_index, style_vars[2] == colonial_index),
        And(style_vars[1] == ranch_index, style_vars[2] == colonial_index)
    ))

    # 7. Arnold is in the second house.
    arnold_index = names.index('Arnold')
    solver.add(name_vars[1] == arnold_index)

    # 8. The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
    ford_index = cars.index('ford f150')
    toyota_index = cars.index('toyota camry')
    solver.add(Or(
        And(car_vars[0] == toyota_index, car_vars[1] == ford_index),
        And(car_vars[0] == toyota_index, car_vars[2] == ford_index),
        And(car_vars[1] == toyota_index, car_vars[2] == ford_index)
    ))

    # 9. The person who has an average height is in the first house.
    average_index = heights.index('average')
    solver.add(height_vars[0] == average_index)

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map house indices to attribute values
        result = []
        for i in range(3):
            name_val = names[model.evaluate(name_vars[i]).as_long()]
            phone_val = phones[model.evaluate(phone_vars[i]).as_long()]
            height_val = heights[model.evaluate(height_vars[i]).as_long()]
            style_val = house_styles[model.evaluate(style_vars[i]).as_long()]
            car_val = cars[model.evaluate(car_vars[i]).as_long()]
            result.append([str(i+1), name_val, phone_val, height_val, style_val, car_val])
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()