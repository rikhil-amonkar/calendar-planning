import z3
import json

def main():
    # Initialize the solver
    solver = z3.Solver()
    
    # Define the attributes and their possible values
    names = ['Peter', 'Arnold', 'Eric']
    cars = ['toyota camry', 'ford f150', 'tesla model 3']
    styles = ['ranch', 'colonial', 'victorian']
    pets = ['cat', 'dog', 'fish']
    occupations = ['engineer', 'doctor', 'teacher']
    vacations = ['city', 'mountain', 'beach']
    
    # Create mappings from attribute values to integers
    name_to_int = {name: idx for idx, name in enumerate(names)}
    car_to_int = {car: idx for idx, car in enumerate(cars)}
    style_to_int = {style: idx for idx, style in enumerate(styles)}
    pet_to_int = {pet: idx for idx, pet in enumerate(pets)}
    occupation_to_int = {occupation: idx for idx, occupation in enumerate(occupations)}
    vacation_to_int = {vacation: idx for idx, vacation in enumerate(vacations)}
    
    # Create inverse mappings for output
    int_to_name = {idx: name for name, idx in name_to_int.items()}
    int_to_car = {idx: car for car, idx in car_to_int.items()}
    int_to_style = {idx: style for style, idx in style_to_int.items()}
    int_to_pet = {idx: pet for pet, idx in pet_to_int.items()}
    int_to_occupation = {idx: occupation for occupation, idx in occupation_to_int.items()}
    int_to_vacation = {idx: vacation for vacation, idx in vacation_to_int.items()}
    
    # Create Z3 variables for each attribute for each house
    house_indices = [1, 2, 3]
    name_vars = [z3.Int(f'name_{i}') for i in house_indices]
    car_vars = [z3.Int(f'car_{i}') for i in house_indices]
    style_vars = [z3.Int(f'style_{i}') for i in house_indices]
    pet_vars = [z3.Int(f'pet_{i}') for i in house_indices]
    occupation_vars = [z3.Int(f'occupation_{i}') for i in house_indices]
    vacation_vars = [z3.Int(f'vacation_{i}') for i in house_indices]
    
    # Add constraints: each attribute must be one of the allowed values
    for i in house_indices:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(z3.And(car_vars[i-1] >= 0, car_vars[i-1] < len(cars)))
        solver.add(z3.And(style_vars[i-1] >= 0, style_vars[i-1] < len(styles)))
        solver.add(z3.And(pet_vars[i-1] >= 0, pet_vars[i-1] < len(pets)))
        solver.add(z3.And(occupation_vars[i-1] >= 0, occupation_vars[i-1] < len(occupations)))
        solver.add(z3.And(vacation_vars[i-1] >= 0, vacation_vars[i-1] < len(vacations)))
    
    # Add constraints: all attributes within a category are distinct
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(car_vars))
    solver.add(z3.Distinct(style_vars))
    solver.add(z3.Distinct(pet_vars))
    solver.add(z3.Distinct(occupation_vars))
    solver.add(z3.Distinct(vacation_vars))
    
    # Clue 1: The person with an aquarium of fish is in the first house.
    solver.add(pet_vars[0] == pet_to_int['fish'])
    
    # Clue 2: The person who owns a Toyota Camry is in the second house.
    solver.add(car_vars[1] == car_to_int['toyota camry'])
    
    # Clue 3: The person who enjoys mountain retreats is not in the second house.
    solver.add(vacation_vars[1] != vacation_to_int['mountain'])
    
    # Clue 4: The person who prefers city breaks is not in the second house.
    solver.add(vacation_vars[1] != vacation_to_int['city'])
    
    # Clue 5: The person in a ranch-style home is somewhere to the left of Peter.
    # Find the house index of ranch and Peter, then ranch_house < peter_house
    ranch_house = z3.Int('ranch_house')
    solver.add(z3.Or([z3.And(style_vars[i] == style_to_int['ranch'], ranch_house == i+1) for i in range(3)]))
    peter_house = z3.Int('peter_house')
    solver.add(z3.Or([z3.And(name_vars[i] == name_to_int['Peter'], peter_house == i+1) for i in range(3)]))
    solver.add(ranch_house < peter_house)
    
    # Clue 6: The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
    # Since Toyota Camry is in house 2 (from clue 2), colonial must be in house 3.
    solver.add(style_vars[2] == style_to_int['colonial'])
    
    # Clue 7: Arnold is the person who has a cat.
    # For the house where name is Arnold, pet is cat.
    for i in range(3):
        solver.add(z3.Implies(name_vars[i] == name_to_int['Arnold'], pet_vars[i] == pet_to_int['cat']))
    
    # Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
    eric_house = z3.Int('eric_house')
    solver.add(z3.Or([z3.And(name_vars[i] == name_to_int['Eric'], eric_house == i+1) for i in range(3)]))
    mountain_house = z3.Int('mountain_house')
    solver.add(z3.Or([z3.And(vacation_vars[i] == vacation_to_int['mountain'], mountain_house == i+1) for i in range(3)]))
    solver.add(eric_house < mountain_house)
    
    # Clue 9: The person who is an engineer is not in the third house.
    solver.add(occupation_vars[2] != occupation_to_int['engineer'])
    
    # Clue 10: The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
    tesla_house = z3.Int('tesla_house')
    solver.add(z3.Or([z3.And(car_vars[i] == car_to_int['tesla model 3'], tesla_house == i+1) for i in range(3)]))
    teacher_house = z3.Int('teacher_house')
    solver.add(z3.Or([z3.And(occupation_vars[i] == occupation_to_int['teacher'], teacher_house == i+1) for i in range(3)]))
    solver.add(tesla_house < teacher_house)
    
    # Clue 11: The person who owns a dog is the person who is an engineer.
    for i in range(3):
        solver.add(z3.Implies(pet_vars[i] == pet_to_int['dog'], occupation_vars[i] == occupation_to_int['engineer']))
    
    # Check if the solver is satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Retrieve the values from the model
        solution_rows = []
        for i in range(3):
            house_num = str(i+1)
            name_val = int_to_name[model.evaluate(name_vars[i]).as_long()]
            car_val = int_to_car[model.evaluate(car_vars[i]).as_long()]
            style_val = int_to_style[model.evaluate(style_vars[i]).as_long()]
            pet_val = int_to_pet[model.evaluate(pet_vars[i]).as_long()]
            occupation_val = int_to_occupation[model.evaluate(occupation_vars[i]).as_long()]
            vacation_val = int_to_vacation[model.evaluate(vacation_vars[i]).as_long()]
            row = [house_num, name_val, car_val, style_val, pet_val, occupation_val, vacation_val]
            solution_rows.append(row)
        
        # Create the JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()