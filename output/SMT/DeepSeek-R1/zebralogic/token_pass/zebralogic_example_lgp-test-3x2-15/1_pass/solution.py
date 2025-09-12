import json
from z3 import *

def main():
    # Define the houses
    houses = [1, 2, 3]
    
    # Define the attributes using EnumSort
    Name, (Arnold, Peter, Eric) = EnumSort('Name', ['Arnold', 'Peter', 'Eric'])
    Height, (short, average, very_short) = EnumSort('Height', ['short', 'average', 'very_short'])
    
    # Create variables for each house's name and height
    name_vars = [Const(f'name_{i}', Name) for i in houses]
    height_vars = [Const(f'height_{i}', Height) for i in houses]
    
    solver = Solver()
    
    # All names and heights are distinct
    solver.add(Distinct(name_vars))
    solver.add(Distinct(height_vars))
    
    # Clue 1: Peter is somewhere to the right of Eric
    eric_positions = []
    peter_positions = []
    for i, name in enumerate(name_vars):
        eric_positions.append(And(name == Eric, i + 1 == 1))
        eric_positions.append(And(name == Eric, i + 1 == 2))
        eric_positions.append(And(name == Eric, i + 1 == 3))
        peter_positions.append(And(name == Peter, i + 1 == 1))
        peter_positions.append(And(name == Peter, i + 1 == 2))
        peter_positions.append(And(name == Peter, i + 1 == 3))
    
    solver.add(Or([
        And(eric_positions[0], Or(peter_positions[1], peter_positions[2])),
        And(eric_positions[1], peter_positions[2])
    ]))
    
    # Clue 2: The person who is short is in the first house
    solver.add(height_vars[0] == short)
    
    # Clue 3: One house between short and very short
    solver.add(Or(
        And(height_vars[0] == short, height_vars[2] == very_short),
        And(height_vars[0] == very_short, height_vars[2] == short)
    ))
    
    # Clue 4: Arnold and very short are adjacent
    for i in range(3):
        for j in range(3):
            if abs(i - j) == 1:
                solver.add(Implies(
                    height_vars[i] == very_short,
                    Or(
                        name_vars[j] == Arnold
                    )
                ))
                solver.add(Implies(
                    name_vars[i] == Arnold,
                    Or(
                        height_vars[j] == very_short
                    )
                ))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in range(3):
            house_num = str(i + 1)
            name_val = model.eval(name_vars[i])
            height_val = model.eval(height_vars[i])
            
            # Convert name to string
            if name_val == Arnold:
                name_str = "Arnold"
            elif name_val == Peter:
                name_str = "Peter"
            else:
                name_str = "Eric"
            
            # Convert height to string
            if height_val == short:
                height_str = "short"
            elif height_val == average:
                height_str = "average"
            else:
                height_str = "very short"
            
            rows.append([house_num, name_str, height_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()