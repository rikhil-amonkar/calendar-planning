from z3 import *

# Create Solver
solver = Solver()

# Define Variables
houses = [1, 2, 3]
names = ['Eric', 'Arnold', 'Peter']
phone_models = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
heights = ['very short', 'average', 'short']
house_styles = ['colonial', 'ranch', 'victorian']
car_models = ['tesla model 3', 'toyota camry', 'ford f150']

# Declare variables for each attribute
name_vars = {h: Int(f'name_{h}') for h in houses}
phone_model_vars = {h: Int(f'phone_model_{h}') for h in houses}
height_vars = {h: Int(f'height_{h}') for h in houses}
house_style_vars = {h: Int(f'house_style_{h}') for h in houses}
car_model_vars = {h: Int(f'car_model_{h}') for h in houses}

# Map strings to integers for constraints
name_map = {n: i for i, n in enumerate(names)}
phone_model_map = {p: i for i, p in enumerate(phone_models)}
height_map = {h: i for i, h in enumerate(heights)}
house_style_map = {hs: i for i, hs in enumerate(house_styles)}
car_model_map = {cm: i for i, cm in enumerate(car_models)}

# Add constraints for unique values per attribute
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(phone_model_vars.values()))
solver.add(Distinct(height_vars.values()))
solver.add(Distinct(house_style_vars.values()))
solver.add(Distinct(car_model_vars.values()))

# Add specific clues as constraints
# Clue 1: Peter is somewhere to the right of Eric.
solver.add(Or(name_vars[2] == name_map['Peter'] and name_vars[1] == name_map['Eric'],
              name_vars[3] == name_map['Peter'] and name_vars[1] == name_map['Eric'],
              name_vars[3] == name_map['Peter'] and name_vars[2] == name_map['Eric']))

# Clue 2: The person living in a colonial-style house is in the second house.
solver.add(house_style_vars[2] == house_style_map['colonial'])

# Clue 3: The person who owns a Tesla Model 3 is the person who is very short.
solver.add(car_model_vars[h] == car_model_map['tesla model 3'] ==>
           height_vars[h] == height_map['very short'] for h in houses)

# Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
solver.add(Or((height_vars[1] == height_map['short'] and phone_model_vars[2] == phone_model_map['samsung galaxy s21']),
              (height_vars[2] == height_map['short'] and phone_model_vars[3] == phone_model_map['samsung galaxy s21'])))

# Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
solver.add(Or((phone_model_vars[1] == phone_model_map['iphone 13'] and phone_model_vars[2] == phone_model_map['google pixel 6']),
              (phone_model_vars[2] == phone_model_map['iphone 13'] and phone_model_vars[3] == phone_model_map['google pixel 6'])))

# Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
solver.add(Or(house_style_vars[2] == house_style_map['colonial'] and house_style_vars[1] == house_style_map['ranch'],
              house_style_vars[3] == house_style_map['colonial'] and house_style_vars[1] == house_style_map['ranch'],
              house_style_vars[3] == house_style_map['colonial'] and house_style_vars[2] == house_style_map['ranch']))

# Clue 7: Arnold is in the second house.
solver.add(name_vars[2] == name_map['Arnold'])

# Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
solver.add(Or(car_model_vars[2] == car_model_map['ford f150'] and car_model_vars[1] == car_model_map['toyota camry'],
              car_model_vars[3] == car_model_map['ford f150'] and car_model_vars[1] == car_model_map['toyota camry'],
              car_model_vars[3] == car_model_map['ford f150'] and car_model_vars[2] == car_model_map['toyota camry']))

# Clue 9: The person who has an average height is in the first house.
solver.add(height_vars[1] == height_map['average'])

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
            "rows": []
        }
    }
    for h in houses:
        name = names[model[name_vars[h]].as_long()]
        phone_model = phone_models[model[phone_model_vars[h]].as_long()]
        height = heights[model[height_vars[h]].as_long()]
        house_style = house_styles[model[house_style_vars[h]].as_long()]
        car_model = car_models[model[car_model_vars[h]].as_long()]
        solution["solution"]["rows"].append([str(h), name, phone_model, height, house_style, car_model])
    
    print(solution)
else:
    print("No solution found")