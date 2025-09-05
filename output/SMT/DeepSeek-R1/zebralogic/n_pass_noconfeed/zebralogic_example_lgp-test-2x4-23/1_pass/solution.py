import json
from z3 import *

def main():
    # Create a solver instance
    solver = Solver()

    # Define the attributes and their possible values
    names = ['Eric', 'Arnold']
    mothers = ['Aniya', 'Holly']
    car_models = ['ford f150', 'tesla model 3']
    heights = ['short', 'very short']

    # Create Z3 variables for each attribute in each house
    # We'll use integers to represent the indices of the values in the lists above
    name_vars = [Int(f"name_{i}") for i in range(2)]
    mother_vars = [Int(f"mother_{i}") for i in range(2)]
    car_vars = [Int(f"car_{i}") for i in range(2)]
    height_vars = [Int(f"height_{i}") for i in range(2)]

    # Add constraints that each attribute variable must be between 0 and 1 (since there are 2 options)
    for var in name_vars + mother_vars + car_vars + height_vars:
        solver.add(var >= 0, var < 2)

    # Each attribute must have distinct values across houses
    solver.add(Distinct(name_vars))
    solver.add(Distinct(mother_vars))
    solver.add(Distinct(car_vars))
    solver.add(Distinct(height_vars))

    # Clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold.
    # Find the house index of Arnold and the house index of Tesla Model 3
    # Tesla Model 3 is at index 1 in car_models
    arnold_index = names.index('Arnold')
    tesla_index = car_models.index('tesla model 3')
    # For each house, if Arnold is in that house, then Tesla must be in a house with higher number
    # Since houses are 0-indexed (0=house1, 1=house2), right means higher index
    for i in range(2):
        for j in range(2):
            if j <= i:
                continue
            # If Arnold is in house i, then Tesla must be in house j
            solver.add(Implies(name_vars[i] == arnold_index, car_vars[j] == tesla_index))

    # Clue 2: Arnold is the person who is short.
    short_index = heights.index('short')
    for i in range(2):
        solver.add(Implies(name_vars[i] == arnold_index, height_vars[i] == short_index))

    # Clue 3: The person whose mother's name is Holly is in the second house.
    holly_index = mothers.index('Holly')
    solver.add(mother_vars[1] == holly_index)

    # Check if the solver is satisfiable
    if solver.check() == sat:
        model = solver.model()
        # Prepare the solution rows
        rows = []
        for i in range(2):
            house_number = str(i+1)
            name_val = names[model.evaluate(name_vars[i]).as_long()]
            mother_val = mothers[model.evaluate(mother_vars[i]).as_long()]
            car_val = car_models[model.evaluate(car_vars[i]).as_long()]
            height_val = heights[model.evaluate(height_vars[i]).as_long()]
            rows.append([house_number, name_val, mother_val, car_val, height_val])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Mother", "CarModel", "Height"],
                "rows": rows
            }
        }
        # Output the JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()