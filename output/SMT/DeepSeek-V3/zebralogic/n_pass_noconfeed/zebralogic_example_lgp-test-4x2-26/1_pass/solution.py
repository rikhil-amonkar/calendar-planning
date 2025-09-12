import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Arnold', 'Eric', 'Peter', 'Alice']
    occupations = ['doctor', 'engineer', 'artist', 'teacher']
    
    # Create variables for name assignments
    name_vars = [Int(f'name_{i}') for i in houses]
    for var in name_vars:
        solver.add(And(var >= 0, var < len(names)))
    
    # Create variables for occupation assignments
    occ_vars = [Int(f'occ_{i}') for i in houses]
    for var in occ_vars:
        solver.add(And(var >= 0, var < len(occupations)))
    
    # All names and occupations are distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(occ_vars))
    
    # Clue 1: There are two houses between Eric and Peter
    eric_idx = names.index('Eric')
    peter_idx = names.index('Peter')
    
    for i in houses:
        for j in houses:
            if abs(i - j) == 3:  # Two houses between means distance of 3
                solver.add(Implies(name_vars[i-1] == eric_idx, name_vars[j-1] == peter_idx))
                solver.add(Implies(name_vars[i-1] == peter_idx, name_vars[j-1] == eric_idx))
    
    # Clue 2: The person who is a teacher is Peter
    teacher_idx = occupations.index('teacher')
    for i in houses:
        solver.add(Implies(occ_vars[i-1] == teacher_idx, name_vars[i-1] == peter_idx))
    
    # Clue 3: Peter is not in the first house
    solver.add(name_vars[0] != peter_idx)
    
    # Clue 4: There is one house between the person who is a doctor and Alice
    doctor_idx = occupations.index('doctor')
    alice_idx = names.index('Alice')
    
    for i in houses:
        for j in houses:
            if abs(i - j) == 2:  # One house between means distance of 2
                solver.add(Implies(occ_vars[i-1] == doctor_idx, name_vars[j-1] == alice_idx))
                solver.add(Implies(name_vars[i-1] == alice_idx, occ_vars[j-1] == doctor_idx))
    
    # Clue 5: The person who is an artist is Alice
    artist_idx = occupations.index('artist')
    for i in houses:
        solver.add(Implies(occ_vars[i-1] == artist_idx, name_vars[i-1] == alice_idx))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for house in houses:
            name_index = model.evaluate(name_vars[house-1]).as_long()
            occ_index = model.evaluate(occ_vars[house-1]).as_long()
            
            solution.append([
                str(house),
                names[name_index],
                occupations[occ_index]
            ])
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Occupation"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()