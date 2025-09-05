import json
from z3 import Solver, Int, And, Distinct, sat

def main():
    solver = Solver()
    
    # There are 2 houses (house indices: 0 for House 1, 1 for House 2)
    # For each house we define three attributes: Name, Birthday, Mother.
    # We map the possible values as follows:
    # Names: 0 = "Arnold", 1 = "Eric"
    # Birthdays: 0 = "april", 1 = "sept"
    # Mothers: 0 = "Aniya", 1 = "Holly"
    
    # Create Z3 integer variables for each attribute in each house.
    name_vars = [Int(f"name_{i+1}") for i in range(2)]
    birthday_vars = [Int(f"birthday_{i+1}") for i in range(2)]
    mother_vars = [Int(f"mother_{i+1}") for i in range(2)]
    
    # Each variable can only be 0 or 1.
    for var in name_vars + birthday_vars + mother_vars:
        solver.add(And(var >= 0, var <= 1))
    
    # All houses must have distinct values for each attribute.
    solver.add(Distinct(name_vars))
    solver.add(Distinct(birthday_vars))
    solver.add(Distinct(mother_vars))
    
    # Clue 2: The person whose birthday is in April is in the first house.
    # Mapping: april = 0
    solver.add(birthday_vars[0] == 0)
    
    # Clue 1: Eric is somewhere to the left of the person whose mother's name is Holly.
    # In 2 houses this forces:
    # - Eric (mapping: 1) must be in the first house.
    # - The person in the house to the right must have mother Holly (mapping: 1).
    solver.add(name_vars[0] == 1)      # House 1 must be Eric.
    solver.add(mother_vars[1] == 1)      # House 2 must have mother Holly.
    
    if solver.check() == sat:
        model = solver.model()
        
        # Define mapping dictionaries to convert from integer values to attributes.
        name_map = {0: "Arnold", 1: "Eric"}
        birthday_map = {0: "april", 1: "sept"}
        mother_map = {0: "Aniya", 1: "Holly"}
        
        rows = []
        for i in range(2):
            house_number = str(i + 1)
            name_val = model[name_vars[i]].as_long()
            birthday_val = model[birthday_vars[i]].as_long()
            mother_val = model[mother_vars[i]].as_long()
            row = [house_number, name_map[name_val], birthday_map[birthday_val], mother_map[mother_val]]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()