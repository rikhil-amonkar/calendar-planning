import z3
import json

def main():
    # Create a solver instance
    solver = z3.Solver()
    
    # Define the house indices (0 to 4 for five houses)
    houses = list(range(5))
    
    # Create enums for names and heights
    NameSort = z3.DeclareSort('Name')
    Peter, Alice, Bob, Eric, Arnold = z3.Consts('Peter Alice Bob Eric Arnold', NameSort)
    names = [Peter, Alice, Bob, Eric, Arnold]
    
    HeightSort = z3.DeclareSort('Height')
    very_tall, average, tall, very_short, short = z3.Consts('very_tall average tall very_short short', HeightSort)
    heights = [very_tall, average, tall, very_short, short]
    
    # Create name and height variables for each house
    name_vars = [z3.Const(f"name_{i}", NameSort) for i in houses]
    height_vars = [z3.Const(f"height_{i}", HeightSort) for i in houses]
    
    # All names and heights are distinct
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(height_vars))
    
    # Each name and height must be one of the defined constants
    for n in name_vars:
        solver.add(z3.Or([n == nm for nm in names]))
    for h in height_vars:
        solver.add(z3.Or([h == ht for ht in heights]))
    
    # Clue 1: The person who is short is in the second house (index 1).
    solver.add(height_vars[1] == short)
    
    # Clue 2: Peter is directly left of Bob.
    for i in range(4):
        solver.add(z3.Implies(name_vars[i] == Peter, name_vars[i+1] == Bob))
    
    # Clue 3: Eric is somewhere to the left of Peter.
    # Create a disjunction over all valid pairs where Eric is left of Peter
    eric_left_of_peter = []
    for i in range(5):
        for j in range(i+1, 5):
            eric_left_of_peter.append(z3.And(name_vars[i] == Eric, name_vars[j] == Peter))
    solver.add(z3.Or(eric_left_of_peter))
    
    # Clue 4: The person who is very tall is directly left of Peter.
    for i in range(4):
        solver.add(z3.Implies(height_vars[i] == very_tall, name_vars[i+1] == Peter))
    
    # Clue 5: Alice is directly left of the person who has an average height.
    for i in range(4):
        solver.add(z3.Implies(name_vars[i] == Alice, height_vars[i+1] == average))
    
    # Clue 6: The person who is short and the person who is very short are next to each other.
    # Since short is in house 2 (index 1), very_short must be in house 1 or 3 (index 0 or 2)
    solver.add(z3.Or(height_vars[0] == very_short, height_vars[2] == very_short))
    
    # Clue 7: The person who has an average height is in the fifth house (index 4).
    solver.add(height_vars[4] == average)
    
    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Map house indices to their solved values
        solution_rows = []
        for i in range(5):
            house_num = str(i+1)
            name_val = str(model.eval(name_vars[i]))
            height_val = str(model.eval(height_vars[i]))
            solution_rows.append([house_num, name_val, height_val])
        
        # Create JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()