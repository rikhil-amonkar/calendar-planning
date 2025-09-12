from z3 import *

# Define the domain of variables
houses = [1, 2, 3]
names = ["Eric", "Arnold", "Peter"]
phone_models = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
heights = ["very short", "average", "short"]
house_styles = ["colonial", "ranch", "victorian"]
car_models = ["tesla model 3", "toyota camry", "ford f150"]

# Create symbolic variables
name_vars = {h: Int(f'name_{h}') for h in houses}
phone_model_vars = {h: Int(f'phone_model_{h}') for h in houses}
height_vars = {h: Int(f'height_{h}') for h in houses}
house_style_vars = {h: Int(f'house_style_{h}') for h in houses}
car_model_vars = {h: Int(f'car_model_{h}') for h in houses}

# Create the solver
solver = Solver()

# Add constraints for uniqueness
for h in houses:
    solver.add(name_vars[h] >= 0)
    solver.add(name_vars[h] < len(names))
    solver.add(phone_model_vars[h] >= 0)
    solver.add(phone_model_vars[h] < len(phone_models))
    solver.add(height_vars[h] >= 0)
    solver.add(height_vars[h] < len(heights))
    solver.add(house_style_vars[h] >= 0)
    solver.add(house_style_vars[h] < len(house_styles))
    solver.add(car_model_vars[h] >= 0)
    solver.add(car_model_vars[h] < len(car_models))

solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([phone_model_vars[h] for h in houses]))
solver.add(Distinct([height_vars[h] for h in houses]))
solver.add(Distinct([house_style_vars[h] for h in houses]))
solver.add(Distinct([car_model_vars[h] for h in houses]))

# Add specific constraints based on clues
# Clue 1: Peter is somewhere to the right of Eric.
solver.add(Or(name_vars[2] == names.index("Peter") & name_vars[1] == names.index("Eric"),
              name_vars[3] == names.index("Peter") & name_vars[1] == names.index("Eric"),
              name_vars[3] == names.index("Peter") & name_vars[2] == names.index("Eric")))

# Clue 2: The person living in a colonial-style house is in the second house.
solver.add(house_style_vars[2] == house_styles.index("colonial"))

# Clue 3: The person who owns a Tesla Model 3 is the person who is very short.
for h in houses:
    solver.add(Implies(car_model_vars[h] == car_models.index("tesla model 3"), 
                       height_vars[h] == heights.index("very short")))

# Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21.
solver.add(Or((height_vars[1] == heights.index("short") & phone_model_vars[2] == phone_models.index("samsung galaxy s21")),
              (height_vars[2] == heights.index("short") & phone_model_vars[3] == phone_models.index("samsung galaxy s21"))))

# Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
solver.add(Or((phone_model_vars[1] == phone_models.index("iphone 13") & phone_model_vars[2] == phone_models.index("google pixel 6")),
              (phone_model_vars[2] == phone_models.index("iphone 13") & phone_model_vars[3] == phone_models.index("google pixel 6"))))

# Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
solver.add(Or(house_style_vars[2] == house_styles.index("colonial") & house_style_vars[1] == house_styles.index("ranch"),
              house_style_vars[3] == house_styles.index("colonial") & house_style_vars[1] == house_styles.index("ranch"),
              house_style_vars[3] == house_styles.index("colonial") & house_style_vars[2] == house_styles.index("ranch")))

# Clue 7: Arnold is in the second house.
solver.add(name_vars[2] == names.index("Arnold"))

# Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
solver.add(Or(car_model_vars[2] == car_models.index("ford f150") & car_model_vars[1] == car_models.index("toyota camry"),
              car_model_vars[3] == car_models.index("ford f150") & car_model_vars[1] == car_models.index("toyota camry"),
              car_model_vars[3] == car_models.index("ford f150") & car_model_vars[2] == car_models.index("toyota camry")))

# Clue 9: The person who has an average height is in the first house.
solver.add(height_vars[1] == heights.index("average"))

# Solve the puzzle
if solver.check() == sat:
    m = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
            "rows": []
        }
    }
    for h in houses:
        name = names[m[name_vars[h]].as_long()]
        phone_model = phone_models[m[phone_model_vars[h]].as_long()]
        height = heights[m[height_vars[h]].as_long()]
        house_style = house_styles[m[house_style_vars[h]].as_long()]
        car_model = car_models[m[car_model_vars[h]].as_long()]
        solution["solution"]["rows"].append([str(h), name, phone_model, height, house_style, car_model])
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")