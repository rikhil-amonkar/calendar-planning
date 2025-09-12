import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define the houses
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Eric', 'Peter', 'Alice', 'Arnold']
    cars = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
    birthdays = ['jan', 'april', 'sept', 'feb']
    hobbies = ['painting', 'cooking', 'gardening', 'photography']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    car_vars = [Int(f'car_{i}') for i in houses]
    birthday_vars = [Int(f'birthday_{i}') for i in houses]
    hobby_vars = [Int(f'hobby_{i}') for i in houses]
    
    # Define domains for each variable
    for i in houses:
        s.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        s.add(And(car_vars[i-1] >= 0, car_vars[i-1] < len(cars)))
        s.add(And(birthday_vars[i-1] >= 0, birthday_vars[i-1] < len(birthdays)))
        s.add(And(hobby_vars[i-1] >= 0, hobby_vars[i-1] < len(hobbies)))
    
    # All attributes must be unique per category
    s.add(Distinct(name_vars))
    s.add(Distinct(car_vars))
    s.add(Distinct(birthday_vars))
    s.add(Distinct(hobby_vars))
    
    # Clue 1: The person whose birthday is in January is not in the second house.
    jan_index = birthdays.index('jan')
    s.add(birthday_vars[1] != jan_index)  # House 2 is index 1
    
    # Clue 2: The photography enthusiast is somewhere to the left of Eric.
    photo_index = hobbies.index('photography')
    eric_index = names.index('Eric')
    s.add(Exists([i, j], And(i < j, hobby_vars[i] == photo_index, name_vars[j] == eric_index)))
    
    # Clue 3: The photography enthusiast is somewhere to the left of Peter.
    peter_index = names.index('Peter')
    s.add(Exists([i, j], And(i < j, hobby_vars[i] == photo_index, name_vars[j] == peter_index)))
    
    # Clue 4: The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
    honda_index = cars.index('honda civic')
    tesla_index = cars.index('tesla model 3')
    for i in range(3):  # Houses 1-3 can be left of another house
        s.add(Implies(car_vars[i] == honda_index, car_vars[i+1] == tesla_index))
    
    # Clue 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
    gardening_index = hobbies.index('gardening')
    for i in range(2):  # Tesla can be 2 positions left of gardening
        s.add(Implies(car_vars[i] == tesla_index, hobby_vars[i+2] == gardening_index))
    for i in range(2, 4):  # Tesla can be 2 positions right of gardening
        s.add(Implies(car_vars[i] == tesla_index, hobby_vars[i-2] == gardening_index))
    
    # Clue 6: The person who owns a Tesla Model 3 is Arnold.
    arnold_index = names.index('Arnold')
    for i in houses:
        s.add(Implies(car_vars[i-1] == tesla_index, name_vars[i-1] == arnold_index))
    
    # Clue 7: The person whose birthday is in February is the person who loves cooking.
    feb_index = birthdays.index('feb')
    cooking_index = hobbies.index('cooking')
    for i in houses:
        s.add(Implies(birthday_vars[i-1] == feb_index, hobby_vars[i-1] == cooking_index))
    
    # Clue 8: The person who owns a Toyota Camry is Peter.
    toyota_index = cars.index('toyota camry')
    for i in houses:
        s.add(Implies(car_vars[i-1] == toyota_index, name_vars[i-1] == peter_index))
    
    # Clue 9: The person whose birthday is in April is Arnold.
    april_index = birthdays.index('april')
    for i in houses:
        s.add(Implies(birthday_vars[i-1] == april_index, name_vars[i-1] == arnold_index))
    
    # Clue 10: Alice is the photography enthusiast.
    alice_index = names.index('Alice')
    for i in houses:
        s.add(Implies(name_vars[i-1] == alice_index, hobby_vars[i-1] == photo_index))
    
    # Clue 11: Peter is the person whose birthday is in January.
    for i in houses:
        s.add(Implies(name_vars[i-1] == peter_index, birthday_vars[i-1] == jan_index))
    
    # Check if solution exists
    if s.check() == sat:
        model = s.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in houses:
            idx = house - 1
            name_val = model.evaluate(name_vars[idx]).as_long()
            car_val = model.evaluate(car_vars[idx]).as_long()
            birthday_val = model.evaluate(birthday_vars[idx]).as_long()
            hobby_val = model.evaluate(hobby_vars[idx]).as_long()
            
            row = [
                str(house),
                names[name_val],
                cars[car_val],
                birthdays[birthday_val],
                hobbies[hobby_val]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()