import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define the houses
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Alice', 'Arnold', 'Eric', 'Peter']
    cars = ['honda civic', 'tesla model 3', 'ford f150', 'toyota camry']
    birthdays = ['sept', 'april', 'feb', 'jan']
    hobbies = ['photography', 'painting', 'cooking', 'gardening']
    
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
    
    # Get indices for easier reference
    alice_idx = names.index('Alice')
    arnold_idx = names.index('Arnold')
    eric_idx = names.index('Eric')
    peter_idx = names.index('Peter')
    
    honda_idx = cars.index('honda civic')
    tesla_idx = cars.index('tesla model 3')
    ford_idx = cars.index('ford f150')
    toyota_idx = cars.index('toyota camry')
    
    sept_idx = birthdays.index('sept')
    april_idx = birthdays.index('april')
    feb_idx = birthdays.index('feb')
    jan_idx = birthdays.index('jan')
    
    photo_idx = hobbies.index('photography')
    painting_idx = hobbies.index('painting')
    cooking_idx = hobbies.index('cooking')
    gardening_idx = hobbies.index('gardening')
    
    # Clue 1: The person whose birthday is in January is not in the second house.
    s.add(birthday_vars[1] != jan_idx)  # House 2 is index 1
    
    # Clue 2: The photography enthusiast is somewhere to the left of Eric.
    # There exists some house i where hobby is photography and some house j > i where name is Eric
    s.add(Or(
        And(hobby_vars[0] == photo_idx, Or(name_vars[1] == eric_idx, name_vars[2] == eric_idx, name_vars[3] == eric_idx)),
        And(hobby_vars[1] == photo_idx, Or(name_vars[2] == eric_idx, name_vars[3] == eric_idx)),
        And(hobby_vars[2] == photo_idx, name_vars[3] == eric_idx)
    ))
    
    # Clue 3: The photography enthusiast is somewhere to the left of Peter.
    s.add(Or(
        And(hobby_vars[0] == photo_idx, Or(name_vars[1] == peter_idx, name_vars[2] == peter_idx, name_vars[3] == peter_idx)),
        And(hobby_vars[1] == photo_idx, Or(name_vars[2] == peter_idx, name_vars[3] == peter_idx)),
        And(hobby_vars[2] == photo_idx, name_vars[3] == peter_idx)
    ))
    
    # Clue 4: The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
    s.add(Or(
        And(car_vars[0] == honda_idx, car_vars[1] == tesla_idx),
        And(car_vars[1] == honda_idx, car_vars[2] == tesla_idx),
        And(car_vars[2] == honda_idx, car_vars[3] == tesla_idx)
    ))
    
    # Clue 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
    s.add(Or(
        And(car_vars[0] == tesla_idx, hobby_vars[2] == gardening_idx),  # Tesla in 1, gardening in 3
        And(car_vars[1] == tesla_idx, hobby_vars[3] == gardening_idx),  # Tesla in 2, gardening in 4
        And(car_vars[2] == tesla_idx, hobby_vars[0] == gardening_idx),  # Tesla in 3, gardening in 1
        And(car_vars[3] == tesla_idx, hobby_vars[1] == gardening_idx)   # Tesla in 4, gardening in 2
    ))
    
    # Clue 6: The person who owns a Tesla Model 3 is Arnold.
    for i in range(4):
        s.add(Implies(car_vars[i] == tesla_idx, name_vars[i] == arnold_idx))
    
    # Clue 7: The person whose birthday is in February is the person who loves cooking.
    for i in range(4):
        s.add(Implies(birthday_vars[i] == feb_idx, hobby_vars[i] == cooking_idx))
    
    # Clue 8: The person who owns a Toyota Camry is Peter.
    for i in range(4):
        s.add(Implies(car_vars[i] == toyota_idx, name_vars[i] == peter_idx))
    
    # Clue 9: The person whose birthday is in April is Arnold.
    for i in range(4):
        s.add(Implies(birthday_vars[i] == april_idx, name_vars[i] == arnold_idx))
    
    # Clue 10: Alice is the photography enthusiast.
    for i in range(4):
        s.add(Implies(name_vars[i] == alice_idx, hobby_vars[i] == photo_idx))
    
    # Clue 11: Peter is the person whose birthday is in January.
    for i in range(4):
        s.add(Implies(name_vars[i] == peter_idx, birthday_vars[i] == jan_idx))
    
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