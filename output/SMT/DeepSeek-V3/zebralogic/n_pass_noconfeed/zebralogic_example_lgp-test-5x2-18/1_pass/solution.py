import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    n_houses = 5
    houses = list(range(1, n_houses+1))
    
    # Define attributes
    names = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
    children = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']
    
    # Create variables for each attribute position
    name_vars = [z3.Int(f'name_{name}') for name in names]
    child_vars = [z3.Int(f'child_{child}') for child in children]
    
    # Each attribute must be in exactly one house (1-5)
    for var in name_vars + child_vars:
        solver.add(z3.And(var >= 1, var <= 5))
    
    # All attributes must have distinct houses
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(child_vars))
    
    # Create mapping for easier access
    name_to_var = dict(zip(names, name_vars))
    child_to_var = dict(zip(children, child_vars))
    
    # Clue 1: Bob is somewhere to the left of the person's child is named Samantha.
    solver.add(name_to_var['Bob'] < child_to_var['Samantha'])
    
    # Clue 2: The person who is the mother of Timothy is somewhere to the left of the person's child is named Samantha.
    solver.add(child_to_var['Timothy'] < child_to_var['Samantha'])
    
    # Clue 3: The person's child is named Fred is in the second house.
    solver.add(child_to_var['Fred'] == 2)
    
    # Clue 4: There is one house between Alice and the person's child is named Samantha.
    solver.add(z3.Or(
        name_to_var['Alice'] == child_to_var['Samantha'] - 2,
        name_to_var['Alice'] == child_to_var['Samantha'] + 2
    ))
    
    # Clue 5: Eric is not in the third house.
    solver.add(name_to_var['Eric'] != 3)
    
    # Clue 6: Bob is not in the third house.
    solver.add(name_to_var['Bob'] != 3)
    
    # Clue 7: The person's child is named Fred is directly left of the person's child is named Bella.
    solver.add(child_to_var['Fred'] == child_to_var['Bella'] - 1)
    
    # Clue 8: The person's child is named Samantha is somewhere to the left of Peter.
    solver.add(child_to_var['Samantha'] < name_to_var['Peter'])
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": []
            }
        }
        
        # Find which name and child is in each house
        house_data = []
        for house in houses:
            house_data.append({"house": house, "name": None, "child": None})
        
        # Populate names
        for name in names:
            house_num = model.eval(name_to_var[name]).as_long()
            for entry in house_data:
                if entry["house"] == house_num:
                    entry["name"] = name
        
        # Populate children
        for child in children:
            house_num = model.eval(child_to_var[child]).as_long()
            for entry in house_data:
                if entry["house"] == house_num:
                    entry["child"] = child
        
        # Create rows in order
        for entry in sorted(house_data, key=lambda x: x["house"]):
            result["solution"]["rows"].append([
                str(entry["house"]),
                entry["name"],
                entry["child"]
            ])
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()