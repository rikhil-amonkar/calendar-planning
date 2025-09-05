import json
from z3 import *

def main():
    # Initialize the solver
    solver = Solver()

    # Define the attributes
    names = ['Eric', 'Arnold', 'Peter']
    phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    heights = ['very short', 'short', 'average']
    styles = ['colonial', 'ranch', 'victorian']
    cars = ['tesla model 3', 'toyota camry', 'ford f150']

    # Create variables for each attribute in each house
    house_names = [Int(f'name_{i}') for i in range(3)]
    house_phones = [Int(f'phone_{i}') for i in range(3)]
    house_heights = [Int(f'height_{i}') for i in range(3)]
    house_styles = [Int(f'style_{i}') for i in range(3)]
    house_cars = [Int(f'car_{i}') for i in range(3)]

    # Constraint: All attributes must be between 0 and 2
    for i in range(3):
        solver.add(And(house_names[i] >= 0, house_names[i] < 3))
        solver.add(And(house_phones[i] >= 0, house_phones[i] < 3))
        solver.add(And(house_heights[i] >= 0, house_heights[i] < 3))
        solver.add(And(house_styles[i] >= 0, house_styles[i] < 3))
        solver.add(And(house_cars[i] >= 0, house_cars[i] < 3))

    # Constraint: All attributes are distinct within their category
    solver.add(Distinct(house_names))
    solver.add(Distinct(house_phones))
    solver.add(Distinct(house_heights))
    solver.add(Distinct(house_styles))
    solver.add(Distinct(house_cars))

    # Clue 1: Peter is somewhere to the right of Eric.
    # Peter is index 2, Eric is index 0 in names list
    eric_index = names.index('Eric')
    peter_index = names.index('Peter')
    solver.add(Or(
        And(house_names[0] == eric_index, Or(house_names[1] == peter_index, house_names[2] == peter_index)),
        And(house_names[1] == eric_index, house_names[2] == peter_index)
    ))

    # Clue 2: The person living in a colonial-style house is in the second house.
    colonial_index = styles.index('colonial')
    solver.add(house_styles[1] == colonial_index)

    # Clue 3: The person who owns a Tesla Model 3 is the person who is very short.
    tesla_index = cars.index('tesla model 3')
    very_short_index = heights.index('very short')
    for i in range(3):
        solver.add(Implies(house_cars[i] == tesla_index, house_heights[i] == very_short_index))

    # Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
    short_index = heights.index('short')
    samsung_index = phones.index('samsung galaxy s21')
    solver.add(Or(
        And(house_heights[0] == short_index, house_phones[1] == samsung_index),
        And(house_heights[1] == short_index, house_phones[2] == samsung_index)
    ))

    # Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
    iphone_index = phones.index('iphone 13')
    pixel_index = phones.index('google pixel 6')
    solver.add(Or(
        And(house_phones[0] == iphone_index, house_phones[1] == pixel_index),
        And(house_phones[1] == iphone_index, house_phones[2] == pixel_index)
    ))

    # Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
    ranch_index = styles.index('ranch')
    solver.add(Or(
        And(house_styles[0] == ranch_index, house_styles[1] == colonial_index),
        And(house_styles[0] == ranch_index, house_styles[2] == colonial_index),
        And(house_styles[1] == ranch_index, house_styles[2] == colonial_index)
    ))

    # Clue 7: Arnold is in the second house.
    arnold_index = names.index('Arnold')
    solver.add(house_names[1] == arnold_index)

    # Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
    ford_index = cars.index('ford f150')
    camry_index = cars.index('toyota camry')
    solver.add(Or(
        And(house_cars[0] == camry_index, Or(house_cars[1] == ford_index, house_cars[2] == ford_index)),
        And(house_cars[1] == camry_index, house_cars[2] == ford_index)
    ))

    # Clue 9: The person who has an average height is in the first house.
    average_index = heights.index('average')
    solver.add(house_heights[0] == average_index)

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map the integer values back to their string attributes
        result = []
        for i in range(3):
            name_val = model.eval(house_names[i]).as_long()
            phone_val = model.eval(house_phones[i]).as_long()
            height_val = model.eval(house_heights[i]).as_long()
            style_val = model.eval(house_styles[i]).as_long()
            car_val = model.eval(house_cars[i]).as_long()
            
            row = [
                str(i+1),
                names[name_val],
                phones[phone_val],
                heights[height_val],
                styles[style_val],
                cars[car_val]
            ]
            result.append(row)
        
        # Format the output as JSON
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