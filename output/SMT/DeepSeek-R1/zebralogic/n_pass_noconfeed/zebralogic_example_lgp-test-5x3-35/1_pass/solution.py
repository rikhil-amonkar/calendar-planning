import z3
import json

def main():
    # Define the attributes and their mappings
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights = ["average", "very short", "short", "very tall", "tall"]
    
    # Create Z3 variables for each house attribute
    name_vars = [z3.Int(f"name_{i}") for i in range(5)]
    mother_vars = [z3.Int(f"mother_{i}") for i in range(5)]
    height_vars = [z3.Int(f"height_{i}") for i in range(5)]
    
    solver = z3.Solver()
    
    # Each attribute must be between 0 and 4 (indices of the possible values)
    for i in range(5):
        solver.add(z3.And(name_vars[i] >= 0, name_vars[i] < 5))
        solver.add(z3.And(mother_vars[i] >= 0, mother_vars[i] < 5))
        solver.add(z3.And(height_vars[i] >= 0, height_vars[i] < 5))
    
    # All attributes are distinct per category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(mother_vars))
    solver.add(z3.Distinct(height_vars))
    
    # Clue 1: Alice is the person whose mother's name is Aniya.
    # Alice is index 3, Aniya is index 2
    for i in range(5):
        solver.add(z3.Implies(name_vars[i] == 3, mother_vars[i] == 2))
    
    # Clue 2: The person who has an average height is somewhere to the left of The person whose mother's name is Penny.
    # average height index 0, Penny index 3
    for i in range(5):
        for j in range(5):
            solver.add(z3.Implies(z3.And(height_vars[i] == 0, mother_vars[j] == 3), i < j))
    
    # Clue 3: The person whose mother's name is Janelle is Bob.
    # Janelle index 1, Bob index 4
    for i in range(5):
        solver.add(z3.Implies(mother_vars[i] == 1, name_vars[i] == 4))
    
    # Clue 4: Peter is not in the second house.
    # Peter index 1, house index 1 (second house is index 1)
    solver.add(name_vars[1] != 1)
    
    # Clue 5: The person who is short is directly left of Arnold.
    # short index 2, Arnold index 2
    for i in range(4):
        solver.add(z3.Implies(height_vars[i] == 2, name_vars[i+1] == 2))
    
    # Clue 6: The person who is very tall is Arnold.
    # very tall index 3, Arnold index 2
    for i in range(5):
        solver.add(z3.Implies(height_vars[i] == 3, name_vars[i] == 2))
    
    # Clue 7: Bob is directly left of the person who has an average height.
    # Bob index 4, average height index 0
    for i in range(4):
        solver.add(z3.Implies(name_vars[i] == 4, height_vars[i+1] == 0))
    
    # Clue 8: Eric is not in the fifth house.
    # Eric index 0, fifth house index 4
    solver.add(name_vars[4] != 0)
    
    # Clue 9: The person who is very tall is somewhere to the right of The person whose mother's name is Holly.
    # very tall index 3, Holly index 4
    for i in range(5):
        for j in range(5):
            solver.add(z3.Implies(z3.And(height_vars[i] == 3, mother_vars[j] == 4), i > j))
    
    # Clue 10: Eric is the person whose mother's name is Kailyn.
    # Eric index 0, Kailyn index 0
    for i in range(5):
        solver.add(z3.Implies(name_vars[i] == 0, mother_vars[i] == 0))
    
    # Clue 11: The person who is very short is in the fifth house.
    # very short index 1, fifth house index 4
    solver.add(height_vars[4] == 1)
    
    # Check if the problem is satisfied
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare the result table
        rows = []
        for i in range(5):
            name_val = model.eval(name_vars[i]).as_long()
            mother_val = model.eval(mother_vars[i]).as_long()
            height_val = model.eval(height_vars[i]).as_long()
            rows.append([str(i+1), names[name_val], mothers[mother_val], heights[height_val]])
        
        # Create the JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Height"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()