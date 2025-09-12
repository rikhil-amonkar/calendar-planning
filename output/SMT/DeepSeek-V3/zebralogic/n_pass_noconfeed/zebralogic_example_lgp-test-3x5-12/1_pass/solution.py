import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Eric', 'Peter', 'Arnold']
    cigars = ['blue master', 'prince', 'pall mall']
    hobbies = ['photography', 'gardening', 'cooking']
    educations = ['high school', 'associate', 'bachelor']
    drinks = ['tea', 'milk', 'water']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    cigar_vars = [z3.Int(f'cigar_{h}') for h in houses]
    hobby_vars = [z3.Int(f'hobby_{h}') for h in houses]
    education_vars = [z3.Int(f'education_{h}') for h in houses]
    drink_vars = [z3.Int(f'drink_{h}') for h in houses]
    
    # Define domains for each variable
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(z3.And(cigar_vars[h-1] >= 0, cigar_vars[h-1] < len(cigars)))
        solver.add(z3.And(hobby_vars[h-1] >= 0, hobby_vars[h-1] < len(hobbies)))
        solver.add(z3.And(education_vars[h-1] >= 0, education_vars[h-1] < len(educations)))
        solver.add(z3.And(drink_vars[h-1] >= 0, drink_vars[h-1] < len(drinks)))
    
    # All attributes are distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(cigar_vars))
    solver.add(z3.Distinct(hobby_vars))
    solver.add(z3.Distinct(education_vars))
    solver.add(z3.Distinct(drink_vars))
    
    # Clue 1: The person partial to Pall Mall is Peter.
    pall_mall_idx = cigars.index('pall mall')
    peter_idx = names.index('Peter')
    for h in houses:
        solver.add(z3.Implies(cigar_vars[h-1] == pall_mall_idx, name_vars[h-1] == peter_idx))
    
    # Clue 2: The person who likes milk is directly left of the person with a high school diploma.
    milk_idx = drinks.index('milk')
    high_school_idx = educations.index('high school')
    for h in range(1, 3):  # Only houses 1 and 2 can be left of someone
        solver.add(z3.Implies(drink_vars[h-1] == milk_idx, education_vars[h] == high_school_idx))
    
    # Clue 3: Eric is the tea drinker.
    eric_idx = names.index('Eric')
    tea_idx = drinks.index('tea')
    for h in houses:
        solver.add(z3.Implies(name_vars[h-1] == eric_idx, drink_vars[h-1] == tea_idx))
    
    # Clue 4: Arnold and the Prince smoker are next to each other.
    arnold_idx = names.index('Arnold')
    prince_idx = cigars.index('prince')
    for h in houses:
        # Check if Arnold is in house h
        arnold_in_h = (name_vars[h-1] == arnold_idx)
        # Prince must be in adjacent house
        adjacent_prince = z3.Or()
        if h > 1:
            adjacent_prince = z3.Or(adjacent_prince, cigar_vars[h-2] == prince_idx)
        if h < 3:
            adjacent_prince = z3.Or(adjacent_prince, cigar_vars[h] == prince_idx)
        solver.add(z3.Implies(arnold_in_h, adjacent_prince))
        
        # Also check the reverse: if Prince is in house h, Arnold must be adjacent
        prince_in_h = (cigar_vars[h-1] == prince_idx)
        adjacent_arnold = z3.Or()
        if h > 1:
            adjacent_arnold = z3.Or(adjacent_arnold, name_vars[h-2] == arnold_idx)
        if h < 3:
            adjacent_arnold = z3.Or(adjacent_arnold, name_vars[h] == arnold_idx)
        solver.add(z3.Implies(prince_in_h, adjacent_arnold))
    
    # Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
    gardening_idx = hobbies.index('gardening')
    for h_prince in range(2, 4):  # Prince can be in house 2 or 3
        for h_gardening in range(1, h_prince):  # Gardening left of prince
            solver.add(z3.Implies(
                z3.And(cigar_vars[h_prince-1] == prince_idx, hobby_vars[h_gardening-1] == gardening_idx),
                h_gardening < h_prince
            ))
    
    # Clue 6: The person who likes milk is the person with an associate's degree.
    associate_idx = educations.index('associate')
    for h in houses:
        solver.add(z3.Implies(drink_vars[h-1] == milk_idx, education_vars[h-1] == associate_idx))
    
    # Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
    bachelor_idx = educations.index('bachelor')
    photography_idx = hobbies.index('photography')
    for h in range(1, 3):  # Only houses 1 and 2 can be left of someone
        solver.add(z3.Implies(education_vars[h-1] == bachelor_idx, hobby_vars[h] == photography_idx))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        header = ["House", "Name", "Cigar", "Hobby", "Education", "Drink"]
        rows = []
        
        for h in houses:
            # Get values from model
            name_val = model.eval(name_vars[h-1]).as_long()
            cigar_val = model.eval(cigar_vars[h-1]).as_long()
            hobby_val = model.eval(hobby_vars[h-1]).as_long()
            education_val = model.eval(education_vars[h-1]).as_long()
            drink_val = model.eval(drink_vars[h-1]).as_long()
            
            # Map indices to actual values
            row = [
                str(h),
                names[name_val],
                cigars[cigar_val],
                hobbies[hobby_val],
                educations[education_val],
                drinks[drink_val]
            ]
            rows.append(row)
        
        # Create JSON output
        solution = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()