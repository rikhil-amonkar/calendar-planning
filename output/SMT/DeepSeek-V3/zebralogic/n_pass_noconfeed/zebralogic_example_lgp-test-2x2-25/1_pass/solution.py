import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Arnold', 'Eric']
    vacations = ['beach', 'mountain']
    
    # Create variables for each attribute per house
    name_vars = {}
    vacation_vars = {}
    
    for house in houses:
        name_vars[house] = z3.Int(f'name_{house}')
        vacation_vars[house] = z3.Int(f'vacation_{house}')
    
    # Constraint: All name variables must be within valid range
    for house in houses:
        solver.add(z3.And(name_vars[house] >= 0, name_vars[house] < len(names)))
        solver.add(z3.And(vacation_vars[house] >= 0, vacation_vars[house] < len(vacations)))
    
    # Constraint: All names are unique
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    
    # Constraint: All vacations are unique
    solver.add(z3.Distinct([vacation_vars[house] for house in houses]))
    
    # Clue 1: Arnold is somewhere to the right of the person who loves beach vacations
    # Find which house has Arnold and which has beach vacation
    arnold_house = z3.Int('arnold_house')
    beach_house = z3.Int('beach_house')
    
    # Arnold is in some house
    solver.add(z3.Or([z3.And(name_vars[house] == names.index('Arnold'), arnold_house == house) for house in houses]))
    
    # Beach vacation is in some house
    solver.add(z3.Or([z3.And(vacation_vars[house] == vacations.index('beach'), beach_house == house) for house in houses]))
    
    # Arnold is to the right of beach vacation person
    solver.add(arnold_house > beach_house)
    
    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare result data
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": []
            }
        }
        
        for house in sorted(houses):
            name_idx = model.evaluate(name_vars[house]).as_long()
            vacation_idx = model.evaluate(vacation_vars[house]).as_long()
            
            row = [
                str(house),
                names[name_idx],
                vacations[vacation_idx]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()