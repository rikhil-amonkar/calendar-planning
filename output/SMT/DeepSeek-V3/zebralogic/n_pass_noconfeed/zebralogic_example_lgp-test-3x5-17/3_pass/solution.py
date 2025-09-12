from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Eric', 'Arnold', 'Peter']
    phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    heights = ['very short', 'short', 'average']
    house_styles = ['colonial', 'ranch', 'victorian']
    car_models = ['tesla model 3', 'toyota camry', 'ford f150']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    phone_vars = [Int(f'phone_{i}') for i in houses]
    height_vars = [Int(f'height_{i}') for i in houses]
    house_style_vars = [Int(f'house_style_{i}') for i in houses]
    car_model_vars = [Int(f'car_model_{i}') for i in houses]
    
    # Define domains for each variable
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(And(phone_vars[i-1] >= 0, phone_vars[i-1] < len(phones)))
        solver.add(And(height_vars[i-1] >= 0, height_vars[i-1] < len(heights)))
        solver.add(And(house_style_vars[i-1] >= 0, house_style_vars[i-1] < len(house_styles)))
        solver.add(And(car_model_vars[i-1] >= 0, car_model_vars[i-1] < len(car_models)))
    
    # All attributes must be unique per category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(phone_vars))
    solver.add(Distinct(height_vars))
    solver.add(Distinct(house_style_vars))
    solver.add(Distinct(car_model_vars))
    
    # Clue 1: Peter is somewhere to the right of Eric
    peter_idx = names.index('Peter')
    eric_idx = names.index('Eric')
    # Create constraints for Peter being right of Eric
    for i in houses:
        for j in houses:
            if i > j:
                solver.add(Implies(name_vars[j-1] == eric_idx, name_vars[i-1] != peter_idx))
    
    # Clue 2: The person living in a colonial-style house is in the second house
    colonial_idx = house_styles.index('colonial')
    solver.add(house_style_vars[1] == colonial_idx)  # house 2 (index 1)
    
    # Clue 3: The person who owns a Tesla Model 3 is the person who is very short
    tesla_idx = car_models.index('tesla model 3')
    very_short_idx = heights.index('very short')
    for i in houses:
        solver.add(Implies(car_model_vars[i-1] == tesla_idx, height_vars[i-1] == very_short_idx))
        solver.add(Implies(height_vars[i-1] == very_short_idx, car_model_vars[i-1] == tesla_idx))
    
    # Clue 4: The person who is short is directly left of the person who uses a Samsung Galaxy S21
    short_idx = heights.index('short')
    samsung_idx = phones.index('samsung galaxy s21')
    for i in range(2):  # houses 1 and 2 can be left of someone
        solver.add(Implies(height_vars[i] == short_idx, 
                          And(i+1 < 3, phone_vars[i+1] == samsung_idx)))
    
    # Clue 5: The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6
    iphone_idx = phones.index('iphone 13')
    pixel_idx = phones.index('google pixel 6')
    for i in range(2):  # houses 1 and 2 can be left of someone
        solver.add(Implies(phone_vars[i] == iphone_idx, 
                          And(i+1 < 3, phone_vars[i+1] == pixel_idx)))
    
    # Clue 6: The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home
    ranch_idx = house_styles.index('ranch')
    # Create constraints for colonial being right of ranch
    for i in houses:
        for j in houses:
            if i > j:
                solver.add(Implies(house_style_vars[j-1] == ranch_idx, house_style_vars[i-1] != colonial_idx))
    
    # Clue 7: Arnold is in the second house
    arnold_idx = names.index('Arnold')
    solver.add(name_vars[1] == arnold_idx)  # house 2 (index 1)
    
    # Clue 8: The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry
    ford_idx = car_models.index('ford f150')
    toyota_idx = car_models.index('toyota camry')
    # Create constraints for Ford being right of Toyota
    for i in houses:
        for j in houses:
            if i > j:
                solver.add(Implies(car_model_vars[j-1] == toyota_idx, car_model_vars[i-1] != ford_idx))
    
    # Clue 9: The person who has an average height is in the first house
    average_idx = heights.index('average')
    solver.add(height_vars[0] == average_idx)  # house 1 (index 0)
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in houses:
            idx = house - 1
            name_val = names[model.evaluate(name_vars[idx]).as_long()]
            phone_val = phones[model.evaluate(phone_vars[idx]).as_long()]
            height_val = heights[model.evaluate(height_vars[idx]).as_long()]
            house_style_val = house_styles[model.evaluate(house_style_vars[idx]).as_long()]
            car_model_val = car_models[model.evaluate(car_model_vars[idx]).as_long()]
            
            result["solution"]["rows"].append([
                str(house),
                name_val,
                phone_val,
                height_val,
                house_style_val,
                car_model_val
            ])
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()