import z3
import json

def main():
    # Define the attributes
    names = ['Arnold', 'Eric']
    birthdays = ['april', 'sept']
    mothers = ['Aniya', 'Holly']
    
    # Create Z3 enums for each attribute type
    Name = z3.EnumSort('Name', names)
    Birthday = z3.EnumSort('Birthday', birthdays)
    Mother = z3.EnumSort('Mother', mothers)
    
    # Create variables for each house's attributes
    name_vars = [z3.Const(f'name_{i}', Name) for i in range(1, 3)]
    birthday_vars = [z3.Const(f'birthday_{i}', Birthday) for i in range(1, 3)]
    mother_vars = [z3.Const(f'mother_{i}', Mother) for i in range(1, 3)]
    
    solver = z3.Solver()
    
    # All attributes must be unique per category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(birthday_vars))
    solver.add(z3.Distinct(mother_vars))
    
    # Clue 1: Eric is to the left of Holly's mother
    eric = z3.Const('Eric', Name)
    holly = z3.Const('Holly', Mother)
    
    # Find house indices for Eric and Holly's mother
    eric_house = z3.Int('eric_house')
    holly_mother_house = z3.Int('holly_mother_house')
    
    # Constrain the house indices
    for i in range(2):
        solver.add(z3.Implies(name_vars[i] == eric, eric_house == i+1))
        solver.add(z3.Implies(mother_vars[i] == holly, holly_mother_house == i+1))
    
    solver.add(eric_house < holly_mother_house)
    
    # Clue 2: April birthday in first house
    april = z3.Const('april', Birthday)
    solver.add(birthday_vars[0] == april)
    
    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract values from model
        solution_rows = []
        for i in range(2):
            name_val = model.eval(name_vars[i])
            birthday_val = model.eval(birthday_vars[i])
            mother_val = model.eval(mother_vars[i])
            
            # Convert Z3 symbols to strings
            row = [
                str(i+1),
                str(name_val),
                str(birthday_val),
                str(mother_val)
            ]
            solution_rows.append(row)
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()