from z3 import *

# Define variables for each attribute for each house
names = [Int(f'name_{i}') for i in range(1, 4)]
phone_models = [Int(f'phone_model_{i}') for i in range(1, 4)]
heights = [Int(f'height_{i}') for i in range(1, 4)]
house_styles = [Int(f'house_style_{i}') for i in range(1, 4)]
car_models = [Int(f'car_model_{i}') for i in range(1, 4)]

# Define domains for each variable
names_domain = [1, 2, 3]  # Eric, Arnold, Peter
phone_models_domain = [1, 2, 3]  # iPhone 13, Samsung Galaxy S21, Google Pixel 6
heights_domain = [1, 2, 3]  # Very short, Average, Short
house_styles_domain = [1, 2, 3]  # Colonial, Ranch, Victorian
car_models_domain = [1, 2, 3]  # Tesla Model 3, Toyota Camry, Ford F-150

# Create solver instance
solver = Solver()

# Add domain constraints
for var in names + phone_models + heights + house_styles + car_models:
    solver.add(var >= 1, var <= 3)

# Unique constraints for each attribute across houses
solver.add(Distinct(names))
solver.add(Distinct(phone_models))
solver.add(Distinct(heights))
solver.add(Distinct(house_styles))
solver.add(Distinct(car_models))

# Clue 1: Peter is somewhere to the right of Eric
solver.add(Or(names[1] == 1, Or(names[0] == 1, names[1] == 3)))

# Clue 2: The person living in a colonial-style house is in the second house
solver.add(house_styles[1] == 1)

# Clue 3: The person who owns a Tesla Model 3 is the person who is very short
solver.add(car_models[i] == 1 == heights[i] for i in range(3))

# Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21
solver.add(Or(And(heights[0] == 3, phone_models[1] == 2), And(heights[1] == 3, phone_models[2] == 2)))

# Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6
solver.add(Or(And(phone_models[0] == 1, phone_models[1] == 3), And(phone_models[1] == 1, phone_models[2] == 3)))

# Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home
solver.add(Or(house_styles[0] == 2, house_styles[1] == 2))

# Clue 7: Arnold is in the second house
solver.add(names[1] == 2)

# Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry
solver.add(Or(car_models[0] == 2, Or(car_models[1] == 2, car_models[2] == 2)))

# Clue 9: The person who has an average height is in the first house
solver.add(heights[0] == 2)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Map symbolic values to actual names and attributes
    name_map = {1: "Eric", 2: "Arnold", 3: "Peter"}
    phone_model_map = {1: "iphone 13", 2: "samsung galaxy s21", 3: "google pixel 6"}
    height_map = {1: "very short", 2: "average", 3: "short"}
    house_style_map = {1: "colonial", 2: "ranch", 3: "victorian"}
    car_model_map = {1: "tesla model 3", 2: "toyota camry", 3: "ford f150"}
    
    # Extract and format the solution
    solution_rows = []
    for i in range(3):
        solution_rows.append([
            str(i+1),
            name_map[model[names[i]].as_long()],
            phone_model_map[model[phone_models[i]].as_long()],
            height_map[model[heights[i]].as_long()],
            house_style_map[model[house_styles[i]].as_long()],
            car_model_map[model[car_models[i]].as_long()]
        ])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
            "rows": solution_rows
        }
    }
    
    print(solution)
else:
    print("No solution found")