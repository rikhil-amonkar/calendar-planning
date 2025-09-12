from z3 import *
import json

def main():
    # Initialize solver
    solver = Solver()
    
    # Define the number of houses
    n = 6
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define all attributes
    names = ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter']
    birthdays = ['jan', 'feb', 'mar', 'april', 'may', 'sept']
    foods = ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    heights = ['very short', 'short', 'average', 'tall', 'very tall', 'super tall']
    car_models = ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']
    
    # Create variables for each attribute per house
    name_vars = [Int(f"name_{i}") for i in houses]
    birthday_vars = [Int(f"birthday_{i}") for i in houses]
    food_vars = [Int(f"food_{i}") for i in houses]
    height_vars = [Int(f"height_{i}") for i in houses]
    car_model_vars = [Int(f"car_model_{i}") for i in houses]
    
    # Constraint: All attributes must be within their respective ranges
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(And(birthday_vars[i-1] >= 0, birthday_vars[i-1] < len(birthdays)))
        solver.add(And(food_vars[i-1] >= 0, food_vars[i-1] < len(foods)))
        solver.add(And(height_vars[i-1] >= 0, height_vars[i-1] < len(heights)))
        solver.add(And(car_model_vars[i-1] >= 0, car_model_vars[i-1] < len(car_models)))
    
    # Constraint: All attributes are distinct per category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(birthday_vars))
    solver.add(Distinct(food_vars))
    solver.add(Distinct(height_vars))
    solver.add(Distinct(car_model_vars))
    
    # Helper functions for constraints
    def left_of(a, b):
        return a < b
    
    def directly_left_of(a, b):
        return a == b - 1
    
    def one_house_between(a, b):
        return Or(a == b - 2, a == b + 2)
    
    def two_houses_between(a, b):
        return Or(a == b - 3, a == b + 3)
    
    # Create mapping for attribute values to indices
    name_idx = {name: idx for idx, name in enumerate(names)}
    birthday_idx = {bday: idx for idx, bday in enumerate(birthdays)}
    food_idx = {food: idx for idx, food in enumerate(foods)}
    height_idx = {height: idx for idx, height in enumerate(heights)}
    car_model_idx = {car: idx for idx, car in enumerate(car_models)}
    
    # Add constraints from clues
    # Clue 1: The person who owns a Honda Civic is the person who is short.
    for i in houses:
        solver.add(Implies(car_model_vars[i-1] == car_model_idx['honda civic'], 
                          height_vars[i-1] == height_idx['short']))
    
    # Clue 2: The person who owns a Ford F-150 is in the fifth house.
    solver.add(car_model_vars[4] == car_model_idx['ford f150'])
    
    # Clue 3: The person who loves stir fry is somewhere to the left of Eric.
    eric_house = Int("eric_house")
    solver.add(Distinct([eric_house] + name_vars))
    solver.add(Or([name_vars[i] == name_idx['Eric'] for i in range(n)]))
    for i in houses:
        solver.add(Implies(name_vars[i-1] == name_idx['Eric'], eric_house == i))
    for i in houses:
        solver.add(Implies(food_vars[i-1] == food_idx['stir fry'], left_of(i, eric_house)))
    
    # Clue 4: The person whose birthday is in May is somewhere to the left of Carol.
    carol_house = Int("carol_house")
    solver.add(Distinct([carol_house] + name_vars))
    solver.add(Or([name_vars[i] == name_idx['Carol'] for i in range(n)]))
    for i in houses:
        solver.add(Implies(name_vars[i-1] == name_idx['Carol'], carol_house == i))
    for i in houses:
        solver.add(Implies(birthday_vars[i-1] == birthday_idx['may'], left_of(i, carol_house)))
    
    # Clue 5: The person who is very short is somewhere to the left of the person whose birthday is in April.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(height_vars[i-1] == height_idx['very short'], 
                                  birthday_vars[j-1] == birthday_idx['april']), 
                              left_of(i, j)))
    
    # Clue 6: The person who owns a BMW 3 Series is not in the third house.
    solver.add(car_model_vars[2] != car_model_idx['bmw 3 series'])
    
    # Clue 7: There are two houses between the person who loves stir fry and the person who is a pizza lover.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(food_vars[i-1] == food_idx['stir fry'], 
                                  food_vars[j-1] == food_idx['pizza']), 
                              two_houses_between(i, j)))
    
    # Clue 8: The person who loves the soup is directly left of Eric.
    for i in houses:
        solver.add(Implies(food_vars[i-1] == food_idx['soup'], 
                          directly_left_of(i, eric_house)))
    
    # Clue 9: The person who loves the spaghetti eater and the person whose birthday is in May are next to each other.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(food_vars[i-1] == food_idx['spaghetti'], 
                                  birthday_vars[j-1] == birthday_idx['may']), 
                              Or(i == j-1, i == j+1)))
    
    # Clue 10: Alice is directly left of the person who owns a BMW 3 Series.
    for i in houses:
        solver.add(Implies(name_vars[i-1] == name_idx['Alice'], 
                          And(i < 6, car_model_vars[i] == car_model_idx['bmw 3 series'])))
    
    # Clue 11: The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(car_model_vars[i-1] == car_model_idx['tesla model 3'], 
                                  height_vars[j-1] == height_idx['tall']), 
                              left_of(i, j)))
    
    # Clue 12: The person who is very tall is the person who owns a Toyota Camry.
    for i in houses:
        solver.add(Implies(height_vars[i-1] == height_idx['very tall'], 
                          car_model_vars[i-1] == car_model_idx['toyota camry']))
    
    # Clue 13: Peter is directly left of the person who is a pizza lover.
    for i in houses:
        solver.add(Implies(name_vars[i-1] == name_idx['Peter'], 
                          And(i < 6, food_vars[i] == food_idx['pizza'])))
    
    # Clue 14: The person who loves the stew is not in the third house.
    solver.add(food_vars[2] != food_idx['stew'])
    
    # Clue 15: There is one house between the person whose birthday is in September and the person who is very short.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(birthday_vars[i-1] == birthday_idx['sept'], 
                                  height_vars[j-1] == height_idx['very short']), 
                              one_house_between(i, j)))
    
    # Clue 16: There is one house between the person whose birthday is in March and the person who is super tall.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(birthday_vars[i-1] == birthday_idx['mar'], 
                                  height_vars[j-1] == height_idx['super tall']), 
                              one_house_between(i, j)))
    
    # Clue 17: The person who is tall is Bob.
    for i in houses:
        solver.add(Implies(height_vars[i-1] == height_idx['tall'], 
                          name_vars[i-1] == name_idx['Bob']))
    
    # Clue 18: The person whose birthday is in May is somewhere to the right of Alice.
    alice_house = Int("alice_house")
    solver.add(Distinct([alice_house] + name_vars))
    solver.add(Or([name_vars[i] == name_idx['Alice'] for i in range(n)]))
    for i in houses:
        solver.add(Implies(name_vars[i-1] == name_idx['Alice'], alice_house == i))
    for i in houses:
        solver.add(Implies(birthday_vars[i-1] == birthday_idx['may'], left_of(alice_house, i)))
    
    # Clue 19: The person who is very short is in the fourth house.
    solver.add(height_vars[3] == height_idx['very short'])
    
    # Clue 20: The person whose birthday is in March is the person who is short.
    for i in houses:
        solver.add(Implies(birthday_vars[i-1] == birthday_idx['mar'], 
                          height_vars[i-1] == height_idx['short']))
    
    # Clue 21: Carol is the person who owns a Tesla Model 3.
    for i in houses:
        solver.add(Implies(name_vars[i-1] == name_idx['Carol'], 
                          car_model_vars[i-1] == car_model_idx['tesla model 3']))
    
    # Clue 22: Eric is the person whose birthday is in January.
    for i in houses:
        solver.add(Implies(name_vars[i-1] == name_idx['Eric'], 
                          birthday_vars[i-1] == birthday_idx['jan']))
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the solution
        solution = []
        for i in range(n):
            house_num = i + 1
            name_val = model.eval(name_vars[i]).as_long()
            birthday_val = model.eval(birthday_vars[i]).as_long()
            food_val = model.eval(food_vars[i]).as_long()
            height_val = model.eval(height_vars[i]).as_long()
            car_model_val = model.eval(car_model_vars[i]).as_long()
            
            row = [
                str(house_num),
                names[name_val],
                birthdays[birthday_val],
                foods[food_val],
                heights[height_val],
                car_models[car_model_val]
            ]
            solution.append(row)
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()