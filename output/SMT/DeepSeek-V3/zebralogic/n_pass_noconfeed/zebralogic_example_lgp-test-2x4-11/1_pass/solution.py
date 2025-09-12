import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    
    # Define attributes with their possible values
    names = ['Eric', 'Arnold']
    hobbies = ['gardening', 'photography']
    pets = ['cat', 'dog']
    heights = ['short', 'very short']
    
    # Create variables for each attribute in each house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    hobby_vars = [z3.Int(f'hobby_{h}') for h in houses]
    pet_vars = [z3.Int(f'pet_{h}') for h in houses]
    height_vars = [z3.Int(f'height_{h}') for h in houses]
    
    # Constraint: all attributes must be within their domain
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(z3.And(hobby_vars[h-1] >= 0, hobby_vars[h-1] < len(hobbies)))
        solver.add(z3.And(pet_vars[h-1] >= 0, pet_vars[h-1] < len(pets)))
        solver.add(z3.And(height_vars[h-1] >= 0, height_vars[h-1] < len(heights)))
    
    # Constraint: all attributes are unique within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(hobby_vars))
    solver.add(z3.Distinct(pet_vars))
    solver.add(z3.Distinct(height_vars))
    
    # Clue 1: The person who is very short is the photography enthusiast.
    very_short_idx = heights.index('very short')
    photography_idx = hobbies.index('photography')
    
    for h in houses:
        solver.add(z3.Implies(
            height_vars[h-1] == very_short_idx,
            hobby_vars[h-1] == photography_idx
        ))
    
    # Clue 2: Eric is the person who is very short.
    eric_idx = names.index('Eric')
    
    for h in houses:
        solver.add(z3.Implies(
            name_vars[h-1] == eric_idx,
            height_vars[h-1] == very_short_idx
        ))
    
    # Clue 3: The person who has a cat is somewhere to the right of the person who is very short.
    cat_idx = pets.index('cat')
    
    # Find the house with very short person
    very_short_house = z3.Int('very_short_house')
    solver.add(z3.Or([z3.And(height_vars[h-1] == very_short_idx, very_short_house == h) for h in houses]))
    
    # Find the house with cat
    cat_house = z3.Int('cat_house')
    solver.add(z3.Or([z3.And(pet_vars[h-1] == cat_idx, cat_house == h) for h in houses]))
    
    # Constraint: cat house is to the right of very short house
    solver.add(cat_house > very_short_house)
    
    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": []
            }
        }
        
        for h in houses:
            name_val = names[model.evaluate(name_vars[h-1]).as_long()]
            hobby_val = hobbies[model.evaluate(hobby_vars[h-1]).as_long()]
            pet_val = pets[model.evaluate(pet_vars[h-1]).as_long()]
            height_val = heights[model.evaluate(height_vars[h-1]).as_long()]
            
            solution["solution"]["rows"].append([
                str(h),
                name_val,
                hobby_val,
                pet_val,
                height_val
            ])
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()