from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define the attributes
    houses = [1, 2, 3]
    names = ["Peter", "Arnold", "Eric"]
    car_models = ["toyota camry", "ford f150", "tesla model 3"]
    house_styles = ["ranch", "colonial", "victorian"]
    pets = ["cat", "dog", "fish"]
    occupations = ["engineer", "doctor", "teacher"]
    vacations = ["city", "mountain", "beach"]
    
    # Create variables for each attribute per house
    name_vars = [Int(f"name_{i}") for i in houses]
    car_vars = [Int(f"car_{i}") for i in houses]
    style_vars = [Int(f"style_{i}") for i in houses]
    pet_vars = [Int(f"pet_{i}") for i in houses]
    occupation_vars = [Int(f"occupation_{i}") for i in houses]
    vacation_vars = [Int(f"vacation_{i}") for i in houses]
    
    # Define domains for each variable
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(And(car_vars[i-1] >= 0, car_vars[i-1] < len(car_models)))
        solver.add(And(style_vars[i-1] >= 0, style_vars[i-1] < len(house_styles)))
        solver.add(And(pet_vars[i-1] >= 0, pet_vars[i-1] < len(pets)))
        solver.add(And(occupation_vars[i-1] >= 0, occupation_vars[i-1] < len(occupations)))
        solver.add(And(vacation_vars[i-1] >= 0, vacation_vars[i-1] < len(vacations)))
    
    # All attributes are distinct per category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(car_vars))
    solver.add(Distinct(style_vars))
    solver.add(Distinct(pet_vars))
    solver.add(Distinct(occupation_vars))
    solver.add(Distinct(vacation_vars))
    
    # Clue 1: The person with an aquarium of fish is in the first house.
    solver.add(pet_vars[0] == pets.index("fish"))
    
    # Clue 2: The person who owns a Toyota Camry is in the second house.
    solver.add(car_vars[1] == car_models.index("toyota camry"))
    
    # Clue 3: The person who enjoys mountain retreats is not in the second house.
    solver.add(vacation_vars[1] != vacations.index("mountain"))
    
    # Clue 4: The person who prefers city breaks is not in the second house.
    solver.add(vacation_vars[1] != vacations.index("city"))
    
    # Clue 5: The person in a ranch-style home is somewhere to the left of Peter.
    # Find ranch house position and Peter's position
    ranch_pos = Int("ranch_pos")
    peter_pos = Int("peter_pos")
    solver.add(ranch_pos >= 1, ranch_pos <= 3)
    solver.add(peter_pos >= 1, peter_pos <= 3)
    
    for i in houses:
        solver.add(Implies(style_vars[i-1] == house_styles.index("ranch"), ranch_pos == i))
        solver.add(Implies(name_vars[i-1] == names.index("Peter"), peter_pos == i))
    
    solver.add(ranch_pos < peter_pos)
    
    # Clue 6: The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
    toyota_pos = Int("toyota_pos")
    colonial_pos = Int("colonial_pos")
    solver.add(toyota_pos >= 1, toyota_pos <= 3)
    solver.add(colonial_pos >= 1, colonial_pos <= 3)
    
    for i in houses:
        solver.add(Implies(car_vars[i-1] == car_models.index("toyota camry"), toyota_pos == i))
        solver.add(Implies(style_vars[i-1] == house_styles.index("colonial"), colonial_pos == i))
    
    solver.add(colonial_pos == toyota_pos + 1)
    
    # Clue 7: Arnold is the person who has a cat.
    arnold_pos = Int("arnold_pos")
    cat_pos = Int("cat_pos")
    solver.add(arnold_pos >= 1, arnold_pos <= 3)
    solver.add(cat_pos >= 1, cat_pos <= 3)
    
    for i in houses:
        solver.add(Implies(name_vars[i-1] == names.index("Arnold"), arnold_pos == i))
        solver.add(Implies(pet_vars[i-1] == pets.index("cat"), cat_pos == i))
    
    solver.add(arnold_pos == cat_pos)
    
    # Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
    eric_pos = Int("eric_pos")
    mountain_pos = Int("mountain_pos")
    solver.add(eric_pos >= 1, eric_pos <= 3)
    solver.add(mountain_pos >= 1, mountain_pos <= 3)
    
    for i in houses:
        solver.add(Implies(name_vars[i-1] == names.index("Eric"), eric_pos == i))
        solver.add(Implies(vacation_vars[i-1] == vacations.index("mountain"), mountain_pos == i))
    
    solver.add(eric_pos < mountain_pos)
    
    # Clue 9: The person who is an engineer is not in the third house.
    solver.add(occupation_vars[2] != occupations.index("engineer"))
    
    # Clue 10: The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
    tesla_pos = Int("tesla_pos")
    teacher_pos = Int("teacher_pos")
    solver.add(tesla_pos >= 1, tesla_pos <= 3)
    solver.add(teacher_pos >= 1, teacher_pos <= 3)
    
    for i in houses:
        solver.add(Implies(car_vars[i-1] == car_models.index("tesla model 3"), tesla_pos == i))
        solver.add(Implies(occupation_vars[i-1] == occupations.index("teacher"), teacher_pos == i))
    
    solver.add(tesla_pos < teacher_pos)
    
    # Clue 11: The person who owns a dog is the person who is an engineer.
    dog_pos = Int("dog_pos")
    engineer_pos = Int("engineer_pos")
    solver.add(dog_pos >= 1, dog_pos <= 3)
    solver.add(engineer_pos >= 1, engineer_pos <= 3)
    
    for i in houses:
        solver.add(Implies(pet_vars[i-1] == pets.index("dog"), dog_pos == i))
        solver.add(Implies(occupation_vars[i-1] == occupations.index("engineer"), engineer_pos == i))
    
    solver.add(dog_pos == engineer_pos)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for i in range(3):
            house_num = i + 1
            name_idx = model.evaluate(name_vars[i]).as_long()
            car_idx = model.evaluate(car_vars[i]).as_long()
            style_idx = model.evaluate(style_vars[i]).as_long()
            pet_idx = model.evaluate(pet_vars[i]).as_long()
            occupation_idx = model.evaluate(occupation_vars[i]).as_long()
            vacation_idx = model.evaluate(vacation_vars[i]).as_long()
            
            row = [
                str(house_num),
                names[name_idx],
                car_models[car_idx],
                house_styles[style_idx],
                pets[pet_idx],
                occupations[occupation_idx],
                vacations[vacation_idx]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()