from z3 import *

# Define domains
names = ["Peter", "Arnold", "Eric"]
car_models = ["toyota camry", "ford f150", "tesla model 3"]
house_styles = ["ranch", "colonial", "victorian"]
pets = ["cat", "dog", "fish"]
occupations = ["engineer", "doctor", "teacher"]
vacations = ["city", "mountain", "beach"]

# Create variables for each house
house1_name, house2_name, house3_name = Ints('house1_name house2_name house3_name')
house1_car_model, house2_car_model, house3_car_model = Ints('house1_car_model house2_car_model house3_car_model')
house1_house_style, house2_house_style, house3_house_style = Ints('house1_house_style house2_house_style house3_house_style')
house1_pet, house2_pet, house3_pet = Ints('house1_pet house2_pet house3_pet')
house1_occupation, house2_occupation, house3_occupation = Ints('house1_occupation house2_occupation house3_occupation')
house1_vacation, house2_vacation, house3_vacation = Ints('house1_vacation house2_vacation house3_vacation')

# Create solver instance
solver = Solver()

# Add constraints for uniqueness
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_car_model, house2_car_model, house3_car_model))
solver.add(Distinct(house1_house_style, house2_house_style, house3_house_style))
solver.add(Distinct(house1_pet, house2_pet, house3_pet))
solver.add(Distinct(house1_occupation, house2_occupation, house3_occupation))
solver.add(Distinct(house1_vacation, house2_vacation, house3_vacation))

# Clue 1: Fish is in the first house.
solver.add(house1_pet == pets.index("fish"))

# Clue 2: Toyota Camry is in the second house.
solver.add(house2_car_model == car_models.index("toyota camry"))

# Clue 3: Mountain retreat is not in the second house.
solver.add(house2_vacation != vacations.index("mountain"))

# Clue 4: City break is not in the second house.
solver.add(house2_vacation != vacations.index("city"))

# Clue 5: Ranch is somewhere to the left of Peter.
solver.add(Or((house1_house_style == house_styles.index("ranch") & house2_name != names.index("Peter")),
             (house1_house_style == house_styles.index("ranch") & house3_name != names.index("Peter")),
             (house2_house_style == house_styles.index("ranch") & house3_name != names.index("Peter"))))

# Clue 6: Toyota Camry is directly left of the colonial house.
solver.add(Or((house1_car_model == car_models.index("toyota camry") & house2_house_style == house_styles.index("colonial")),
             (house2_car_model == car_models.index("toyota camry") & house3_house_style == house_styles.index("colonial"))))

# Clue 7: Arnold has a cat.
solver.add(house1_pet == pets.index("cat") | house2_pet == pets.index("cat") | house3_pet == pets.index("cat"))
solver.add(house1_name == names.index("Arnold") == house1_pet == pets.index("cat") |
           house2_name == names.index("Arnold") == house2_pet == pets.index("cat") |
           house3_name == names.index("Arnold") == house3_pet == pets.index("cat"))

# Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
solver.add(Or((house1_name == names.index("Eric") & (house2_vacation == vacations.index("mountain") | house3_vacation == vacations.index("mountain"))),
             (house2_name == names.index("Eric") & house3_vacation == vacations.index("mountain"))))

# Clue 9: Engineer is not in the third house.
solver.add(house3_occupation != occupations.index("engineer"))

# Clue 10: Tesla Model 3 is somewhere to the left of the teacher.
solver.add(Or((house1_car_model == car_models.index("tesla model 3") & (house2_occupation == occupations.index("teacher") | house3_occupation == occupations.index("teacher"))),
             (house2_car_model == car_models.index("tesla model 3") & house3_occupation == occupations.index("teacher"))))

# Clue 11: Dog owner is the engineer.
solver.add(Or((house1_pet == pets.index("dog") & house1_occupation == occupations.index("engineer")),
             (house2_pet == pets.index("dog") & house2_occupation == occupations.index("engineer")),
             (house3_pet == pets.index("dog") & house3_occupation == occupations.index("engineer"))))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": []
        }
    }
    for i in range(3):
        house_number = str(i + 1)
        name = names[model.eval(Int(f'house{i+1}_name')).as_long()]
        car_model = car_models[model.eval(Int(f'house{i+1}_car_model')).as_long()]
        house_style = house_styles[model.eval(Int(f'house{i+1}_house_style')).as_long()]
        pet = pets[model.eval(Int(f'house{i+1}_pet')).as_long()]
        occupation = occupations[model.eval(Int(f'house{i+1}_occupation')).as_long()]
        vacation = vacations[model.eval(Int(f'house{i+1}_vacation')).as_long()]
        solution["solution"]["rows"].append([house_number, name, car_model, house_style, pet, occupation, vacation])
    print(solution)
else:
    print("No solution found")