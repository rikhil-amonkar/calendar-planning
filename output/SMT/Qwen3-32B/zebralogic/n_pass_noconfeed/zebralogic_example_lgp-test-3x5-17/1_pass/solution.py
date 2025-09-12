from z3 import *
import json

# Define EnumSorts for each attribute category
Names, (Eric, Arnold, Peter) = EnumSort('Names', ['Eric', 'Arnold', 'Peter'])
Phones, (iphone_13, samsung_galaxy_s21, google_pixel_6) = EnumSort('Phones', ['iphone_13', 'samsung_galaxy_s21', 'google_pixel_6'])
Heights, (very_short, average, short) = EnumSort('Heights', ['very_short', 'average', 'short'])
HouseStyles, (colonial, ranch, victorian) = EnumSort('HouseStyles', ['colonial', 'ranch', 'victorian'])
Cars, (tesla_model_3, toyota_camry, ford_f150) = EnumSort('Cars', ['tesla_model_3', 'toyota_camry', 'ford_f150'])

# Create variables for each house (1, 2, 3)
# House 1
name_1 = Const('name_1', Names)
phone_1 = Const('phone_1', Phones)
height_1 = Const('height_1', Heights)
style_1 = Const('style_1', HouseStyles)
car_1 = Const('car_1', Cars)

# House 2
name_2 = Const('name_2', Names)
phone_2 = Const('phone_2', Phones)
height_2 = Const('height_2', Heights)
style_2 = Const('style_2', HouseStyles)
car_2 = Const('car_2', Cars)

# House 3
name_3 = Const('name_3', Names)
phone_3 = Const('phone_3', Phones)
height_3 = Const('height_3', Heights)
style_3 = Const('style_3', HouseStyles)
car_3 = Const('car_3', Cars)

# Initialize solver
solver = Solver()

# Add distinct constraints for each category
solver.add(Distinct(name_1, name_2, name_3))
solver.add(Distinct(phone_1, phone_2, phone_3))
solver.add(Distinct(height_1, height_2, height_3))
solver.add(Distinct(style_1, style_2, style_3))
solver.add(Distinct(car_1, car_2, car_3))

# Add constraints based on clues
# Clue 2: colonial-style house is in the second house
solver.add(style_2 == colonial)

# Clue 7: Arnold is in the second house
solver.add(name_2 == Arnold)

# Clue 9: average height is in the first house
solver.add(height_1 == average)

# Clue 6: colonial is to the right of ranch => ranch is in house 1
solver.add(style_1 == ranch)

# Clue 1: Peter is to the right of Eric
solver.add(Or(name_1 != Eric, Or(name_2 == Peter, name_3 == Peter)))
solver.add(Or(name_2 != Eric, name_3 == Peter))
solver.add(name_3 != Eric)

# Clue 3: Tesla owner is very short
solver.add((car_1 == tesla_model_3) == (height_1 == very_short))
solver.add((car_2 == tesla_model_3) == (height_2 == very_short))
solver.add((car_3 == tesla_model_3) == (height_3 == very_short))

# Clue 4: short is directly left of Samsung Galaxy S21
solver.add(Or(
    And(height_1 == short, phone_2 == samsung_galaxy_s21),
    And(height_2 == short, phone_3 == samsung_galaxy_s21)
))

# Clue 5: iPhone 13 is directly left of Google Pixel 6
solver.add(Or(
    And(phone_1 == iphone_13, phone_2 == google_pixel_6),
    And(phone_2 == iphone_13, phone_3 == google_pixel_6)
))

# Clue 8: Ford F-150 is to the right of Toyota Camry
solver.add(Or(car_1 != toyota_camry, Or(car_2 == ford_f150, car_3 == ford_f150)))
solver.add(Or(car_2 != toyota_camry, car_3 == ford_f150))
solver.add(car_3 != toyota_camry)

# Check for solution
if solver.check() == sat:
    model = solver.model()
    rows = []
    for house_num in [1, 2, 3]:
        if house_num == 1:
            name, phone, height, style, car = name_1, phone_1, height_1, style_1, car_1
        elif house_num == 2:
            name, phone, height, style, car = name_2, phone_2, height_2, style_2, car_2
        else:
            name, phone, height, style, car = name_3, phone_3, height_3, style_3, car_3

        name_val = model.evaluate(name).decl().name()
        phone_val = model.evaluate(phone).decl().name()
        height_val = model.evaluate(height).decl().name()
        style_val = model.evaluate(style).decl().name()
        car_val = model.evaluate(car).decl().name()

        # Format phone and car names to match problem statement
        if phone_val == 'iphone_13':
            phone_str = 'iphone 13'
        elif phone_val == 'samsung_galaxy_s21':
            phone_str = 'samsung galaxy s21'
        elif phone_val == 'google_pixel_6':
            phone_str = 'google pixel 6'
        else:
            phone_str = phone_val

        if car_val == 'ford_f150':
            car_str = 'ford f150'
        elif car_val == 'toyota_camry':
            car_str = 'toyota camry'
        elif car_val == 'tesla_model_3':
            car_str = 'tesla model 3'
        else:
            car_str = car_val

        rows.append([str(house_num), name_val, phone_str, height_val, style_val, car_str])

    solution = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
            "rows": rows
        }
    }

    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")