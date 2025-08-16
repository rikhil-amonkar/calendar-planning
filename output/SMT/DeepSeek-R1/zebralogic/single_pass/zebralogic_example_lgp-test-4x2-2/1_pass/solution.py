from z3 import *
import json

def main():
    # Define enums for names and styles
    Name, (Arnold, Peter, Eric, Alice) = EnumSort('Name', ['Arnold', 'Peter', 'Eric', 'Alice'])
    Style, (victorian, ranch, colonial, craftsman) = EnumSort('Style', ['victorian', 'ranch', 'colonial', 'craftsman'])
    
    # Create variables for each house: name and style
    names = [Const('n1', Name), Const('n2', Name), Const('n3', Name), Const('n4', Name)]
    styles = [Const('s1', Style), Const('s2', Style), Const('s3', Style), Const('s4', Style)]
    
    solver = Solver()
    
    # All names and styles are distinct
    solver.add(Distinct(names))
    solver.add(Distinct(styles))
    
    # Clue 3: Eric is in the third house
    solver.add(names[2] == Eric)
    # Clue 4: Arnold is in the fourth house
    solver.add(names[3] == Arnold)
    # Clue 1: Eric is in a Craftsman house (third house)
    solver.add(styles[2] == craftsman)
    
    # Clue 5: The Victorian house is occupied by Alice
    solver.add(Or(
        And(styles[0] == victorian, names[0] == Alice),
        And(styles[1] == victorian, names[1] == Alice),
        And(styles[2] == victorian, names[2] == Alice),
        And(styles[3] == victorian, names[3] == Alice)
    ))
    
    # Clue 2: Ranch is directly left of Victorian
    solver.add(Or(
        And(styles[0] == ranch, styles[1] == victorian),
        And(styles[1] == ranch, styles[2] == victorian),
        And(styles[2] == ranch, styles[3] == victorian)
    ))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in range(4):
            house_num = str(i + 1)
            name_val = model.eval(names[i])
            style_val = model.eval(styles[i])
            rows.append([house_num, str(name_val), str(style_val)])
        
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()