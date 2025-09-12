import json
from z3 import *

def main():
    solver = Solver()
    
    # Define the attributes for each house
    houses = [1, 2]
    
    # Create Z3 variables for each attribute per house
    name = [Int(f'name_{i}') for i in houses]
    food = [Int(f'food_{i}') for i in houses]
    mother = [Int(f'mother_{i}') for i in houses]
    
    # Define value mappings
    name_values = {'Arnold': 0, 'Eric': 1}
    food_values = {'grilled cheese': 0, 'pizza': 1}
    mother_values = {'Holly': 0, 'Aniya': 1}
    
    # Add constraints for each attribute domain
    for i in houses:
        solver.add(name[i-1] >= 0, name[i-1] <= 1)
        solver.add(food[i-1] >= 0, food[i-1] <= 1)
        solver.add(mother[i-1] >= 0, mother[i-1] <= 1)
    
    # All attributes must have distinct values across houses
    solver.add(Distinct(name))
    solver.add(Distinct(food))
    solver.add(Distinct(mother))
    
    # Clue 1: Grilled cheese left of pizza lover
    solver.add(food[0] == food_values['grilled cheese'])
    solver.add(food[1] == food_values['pizza'])
    
    # Clue 2: Arnold not in second house
    solver.add(name[0] == name_values['Arnold'])
    
    # Clue 3: Arnold's mother is Holly
    solver.add(mother[0] == mother_values['Holly'])
    
    # Check solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map back to string values
        reverse_name = {v: k for k, v in name_values.items()}
        reverse_food = {v: k for k, v in food_values.items()}
        reverse_mother = {v: k for k, v in mother_values.items()}
        
        rows = []
        for i in houses:
            idx = i-1
            n_val = model.evaluate(name[idx]).as_long()
            f_val = model.evaluate(food[idx]).as_long()
            m_val = model.evaluate(mother[idx]).as_long()
            
            rows.append([
                str(i),
                reverse_name[n_val],
                reverse_food[f_val],
                reverse_mother[m_val]
            ])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()