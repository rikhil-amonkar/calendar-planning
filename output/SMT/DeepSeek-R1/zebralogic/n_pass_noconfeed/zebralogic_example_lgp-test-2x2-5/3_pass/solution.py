import z3
import json

def main():
    # Create a solver instance
    solver = z3.Solver()
    
    # Define the number of houses
    num_houses = 2
    
    # Create enums for attributes and unpack the sort and constants
    NameSort, (eric, arnold) = z3.EnumSort('Name', ['Eric', 'Arnold'])
    HouseStyleSort, (victorian, colonial) = z3.EnumSort('HouseStyle', ['victorian', 'colonial'])
    
    # Create variables for each house using the correct sorts
    names = [z3.Const(f'name_{i}', NameSort) for i in range(1, num_houses+1)]
    styles = [z3.Const(f'style_{i}', HouseStyleSort) for i in range(1, num_houses+1)]
    
    # Each attribute is unique
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(styles))
    
    # Clue 1: Victorian house is left of colonial house
    solver.add(styles[0] == victorian)
    solver.add(styles[1] == colonial)
    
    # Clue 2: Eric is in the first house
    solver.add(names[0] == eric)
    
    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare results
        rows = []
        for i in range(num_houses):
            house_num = str(i+1)
            # Evaluate name and style for current house
            name_val = model.eval(names[i])
            style_val = model.eval(styles[i])
            # Convert to string and handle enum naming by taking the last part after '::'
            name_str = str(name_val).split('::')[-1]
            style_str = str(style_val).split('::')[-1]
            rows.append([house_num, name_str, style_str])
        
        # Construct JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()