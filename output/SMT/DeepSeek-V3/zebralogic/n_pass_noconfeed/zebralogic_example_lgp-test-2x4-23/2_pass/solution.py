import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    h_range = range(len(houses))
    
    # Define attributes with their possible values
    names = ['Eric', 'Arnold']
    mothers = ['Aniya', 'Holly']
    car_models = ['ford f150', 'tesla model 3']
    heights = ['short', 'very short']
    
    # Create variables for each attribute in each house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    mother_vars = [z3.Int(f'mother_{h}') for h in houses]
    car_vars = [z3.Int(f'car_{h}') for h in houses]
    height_vars = [z3.Int(f'height_{h}') for h in houses]
    
    # Define value mappings
    name_map = {0: 'Eric', 1: 'Arnold'}
    mother_map = {0: 'Aniya', 1: 'Holly'}
    car_map = {0: 'ford f150', 1: 'tesla model 3'}
    height_map = {0: 'short', 1: 'very short'}
    
    # Constraint: All attributes must be within valid range
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(z3.And(mother_vars[h-1] >= 0, mother_vars[h-1] < len(mothers)))
        solver.add(z3.And(car_vars[h-1] >= 0, car_vars[h-1] < len(car_models)))
        solver.add(z3.And(height_vars[h-1] >= 0, height_vars[h-1] < len(heights)))
    
    # Constraint: All attributes must be unique within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(mother_vars))
    solver.add(z3.Distinct(car_vars))
    solver.add(z3.Distinct(height_vars))
    
    # Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
    # Create variables to represent Arnold's house and Tesla house
    arnold_house = z3.Int('arnold_house')
    tesla_house = z3.Int('tesla_house')
    
    # Arnold is in exactly one house
    arnold_constraints = []
    for h in houses:
        arnold_constraints.append(z3.And(name_vars[h-1] == 1, arnold_house == h))
    solver.add(z3.Or(arnold_constraints))
    
    # Tesla is in exactly one house
    tesla_constraints = []
    for h in houses:
        tesla_constraints.append(z3.And(car_vars[h-1] == 1, tesla_house == h))
    solver.add(z3.Or(tesla_constraints))
    
    # Tesla house > Arnold house
    solver.add(tesla_house > arnold_house)
    
    # Clue 2: Arnold is the person who is short.
    for h in houses:
        solver.add(z3.Implies(name_vars[h-1] == 1, height_vars[h-1] == 0))
    
    # Clue 3: The person whose mother's name is Holly is in the second house.
    # Holly is value 1, house 2 is index 1
    solver.add(mother_vars[1] == 1)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Mother", "CarModel", "Height"],
                "rows": []
            }
        }
        
        for h in houses:
            name_val = model.eval(name_vars[h-1]).as_long()
            mother_val = model.eval(mother_vars[h-1]).as_long()
            car_val = model.eval(car_vars[h-1]).as_long()
            height_val = model.eval(height_vars[h-1]).as_long()
            
            row = [
                str(h),
                name_map[name_val],
                mother_map[mother_val],
                car_map[car_val],
                height_map[height_val]
            ]
            solution_data["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()