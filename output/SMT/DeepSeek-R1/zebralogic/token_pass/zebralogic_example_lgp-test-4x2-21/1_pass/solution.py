import json
from z3 import *

def main():
    # Define the attributes
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    styles = ['craftsman', 'colonial', 'ranch', 'victorian']
    
    # Create Z3 enums for names and styles
    Name = Datatype('Name')
    for name in names:
        Name.declare(name)
    Name = Name.create()
    
    Style = Datatype('Style')
    for style in styles:
        Style.declare(style)
    Style = Style.create()
    
    # Create variables for each house's name and style
    n = [Const(f'n_{i}', Name) for i in range(4)]
    s = [Const(f's_{i}', Style) for i in range(4)]
    
    solver = Solver()
    
    # All names and styles are distinct
    solver.add(Distinct(n))
    solver.add(Distinct(s))
    
    # Clue 1: Alice is in the second house
    solver.add(n[1] == Name.Alice)
    
    # Clue 2: Victorian house directly left of Peter
    for i in range(3):
        solver.add(Implies(s[i] == Style.victorian, n[i+1] == Name.Peter))
    
    # Clue 3: Peter right of ranch house
    ranch_index = Int('ranch_index')
    peter_index = Int('peter_index')
    solver.add(ranch_index >= 0, ranch_index < 4)
    solver.add(peter_index >= 0, peter_index < 4)
    for i in range(4):
        solver.add(If(s[i] == Style.ranch, ranch_index == i, True))
        solver.add(If(n[i] == Name.Peter, peter_index == i, True))
    solver.add(peter_index > ranch_index)
    
    # Clue 4: Arnold right of Craftsman house
    craftsman_index = Int('craftsman_index')
    arnold_index = Int('arnold_index')
    solver.add(craftsman_index >= 0, craftsman_index < 4)
    solver.add(arnold_index >= 0, arnold_index < 4)
    for i in range(4):
        solver.add(If(s[i] == Style.craftsman, craftsman_index == i, True))
        solver.add(If(n[i] == Name.Arnold, arnold_index == i, True))
    solver.add(arnold_index > craftsman_index)
    
    # Clue 5: Craftsman house is Alice
    for i in range(4):
        solver.add(Implies(s[i] == Style.craftsman, n[i] == Name.Alice))
    
    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the solution
        result = []
        for i in range(4):
            name_val = model.eval(n[i])
            style_val = model.eval(s[i])
            result.append([str(i+1), str(name_val), str(style_val)])
        
        # Format as JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": result
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()