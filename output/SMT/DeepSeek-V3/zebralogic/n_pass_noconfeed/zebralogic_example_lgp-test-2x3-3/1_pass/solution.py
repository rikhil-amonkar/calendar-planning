import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    
    # Define attributes with their possible values
    names = ['Arnold', 'Eric']
    foods = ['grilled cheese', 'pizza']
    mothers = ['Holly', 'Aniya']
    
    # Create variables for each attribute in each house
    name_vars = {house: z3.Int(f'name_{house}') for house in houses}
    food_vars = {house: z3.Int(f'food_{house}') for house in houses}
    mother_vars = {house: z3.Int(f'mother_{house}') for house in houses}
    
    # Constraint: All attributes within each category must be distinct
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    solver.add(z3.Distinct([food_vars[house] for house in houses]))
    solver.add(z3.Distinct([mother_vars[house] for house in houses]))
    
    # Constraint: All variables must be within valid range (0-indexed)
    for house in houses:
        solver.add(name_vars[house] >= 0, name_vars[house] < len(names))
        solver.add(food_vars[house] >= 0, food_vars[house] < len(foods))
        solver.add(mother_vars[house] >= 0, mother_vars[house] < len(mothers))
    
    # Clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
    grilled_cheese_idx = foods.index('grilled cheese')
    pizza_idx = foods.index('pizza')
    solver.add(food_vars[1] == grilled_cheese_idx, food_vars[2] == pizza_idx)
    
    # Clue 2: Arnold is not in the second house.
    arnold_idx = names.index('Arnold')
    solver.add(name_vars[2] != arnold_idx)
    
    # Clue 3: Arnold is the person whose mother's name is Holly.
    holly_idx = mothers.index('Holly')
    # Arnold's house has mother Holly
    for house in houses:
        solver.add(z3.Implies(name_vars[house] == arnold_idx, mother_vars[house] == holly_idx))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare result data
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for house in sorted(houses):
            name_val = names[model.evaluate(name_vars[house]).as_long()]
            food_val = foods[model.evaluate(food_vars[house]).as_long()]
            mother_val = mothers[model.evaluate(mother_vars[house]).as_long()]
            
            solution["solution"]["rows"].append([
                str(house),
                name_val,
                food_val,
                mother_val
            ])
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()