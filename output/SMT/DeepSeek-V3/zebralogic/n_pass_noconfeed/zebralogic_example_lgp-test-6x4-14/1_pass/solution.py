from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define the number of houses
    n = 6
    houses = range(1, n+1)
    
    # Define all attributes
    names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    car_models = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']
    
    # Create integer variables for each attribute
    name_vars = [Int(f'name_{name}') for name in names]
    car_vars = [Int(f'car_{car}') for car in car_models]
    mother_vars = [Int(f'mother_{mother}') for mother in mothers]
    hobby_vars = [Int(f'hobby_{hobby}') for hobby in hobbies]
    
    # Each attribute must be in a house (1-6)
    for var in name_vars + car_vars + mother_vars + hobby_vars:
        solver.add(And(var >= 1, var <= n))
    
    # All attributes of the same type must be distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(car_vars))
    solver.add(Distinct(mother_vars))
    solver.add(Distinct(hobby_vars))
    
    # Create mappings for easier constraint writing
    name_to_var = dict(zip(names, name_vars))
    car_to_var = dict(zip(car_models, car_vars))
    mother_to_var = dict(zip(mothers, mother_vars))
    hobby_to_var = dict(zip(hobbies, hobby_vars))
    
    # Clue 1: The person who owns a Toyota Camry is in the sixth house.
    solver.add(car_to_var['toyota camry'] == 6)
    
    # Clue 2: Carol is the photography enthusiast.
    solver.add(name_to_var['Carol'] == hobby_to_var['photography'])
    
    # Clue 3: The person who owns a Chevrolet Silverado is The person whose mother's name is Aniya.
    solver.add(car_to_var['chevrolet silverado'] == mother_to_var['Aniya'])
    
    # Clue 4: The person who owns a Chevrolet Silverado is not in the second house.
    solver.add(car_to_var['chevrolet silverado'] != 2)
    
    # Clue 5: The person who owns a Ford F-150 is The person whose mother's name is Sarah.
    solver.add(car_to_var['ford f150'] == mother_to_var['Sarah'])
    
    # Clue 6: The person who owns a BMW 3 Series is Bob.
    solver.add(car_to_var['bmw 3 series'] == name_to_var['Bob'])
    
    # Clue 7: The person whose mother's name is Kailyn is in the sixth house.
    solver.add(mother_to_var['Kailyn'] == 6)
    
    # Clue 8: Eric is directly left of the person who enjoys knitting.
    solver.add(name_to_var['Eric'] == hobby_to_var['knitting'] - 1)
    
    # Clue 9: There is one house between The person whose mother's name is Sarah and the person who owns a Toyota Camry.
    solver.add(Or(
        mother_to_var['Sarah'] == car_to_var['toyota camry'] - 2,
        mother_to_var['Sarah'] == car_to_var['toyota camry'] + 2
    ))
    
    # Clue 10: The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
    solver.add(mother_to_var['Penny'] > hobby_to_var['knitting'])
    
    # Clue 11: The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
    solver.add(mother_to_var['Aniya'] > car_to_var['honda civic'])
    
    # Clue 12: Alice is somewhere to the right of the person who owns a Ford F-150.
    solver.add(name_to_var['Alice'] > car_to_var['ford f150'])
    
    # Clue 13: Eric is the person who enjoys gardening.
    solver.add(name_to_var['Eric'] == hobby_to_var['gardening'])
    
    # Clue 14: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    solver.add(hobby_to_var['woodworking'] < hobby_to_var['knitting'])
    
    # Clue 15: There is one house between The person whose mother's name is Sarah and the person who loves cooking.
    solver.add(Or(
        mother_to_var['Sarah'] == hobby_to_var['cooking'] - 2,
        mother_to_var['Sarah'] == hobby_to_var['cooking'] + 2
    ))
    
    # Clue 16: The person who owns a Honda Civic is Arnold.
    solver.add(car_to_var['honda civic'] == name_to_var['Arnold'])
    
    # Clue 17: The person whose mother's name is Holly is directly left of the person who enjoys knitting.
    solver.add(mother_to_var['Holly'] == hobby_to_var['knitting'] - 1)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": []
            }
        }
        
        # For each house, find the attributes
        for house in houses:
            row = [str(house)]
            
            # Find name for this house
            for name in names:
                if model.eval(name_to_var[name]).as_long() == house:
                    row.append(name)
                    break
            
            # Find car for this house
            for car in car_models:
                if model.eval(car_to_var[car]).as_long() == house:
                    row.append(car)
                    break
            
            # Find mother for this house
            for mother in mothers:
                if model.eval(mother_to_var[mother]).as_long() == house:
                    row.append(mother)
                    break
            
            # Find hobby for this house
            for hobby in hobbies:
                if model.eval(hobby_to_var[hobby]).as_long() == house:
                    row.append(hobby)
                    break
            
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()