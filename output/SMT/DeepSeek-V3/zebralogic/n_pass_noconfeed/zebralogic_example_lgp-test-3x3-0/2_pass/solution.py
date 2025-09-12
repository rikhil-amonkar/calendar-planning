import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Peter', 'Eric', 'Arnold']
    educations = ['bachelor', 'associate', 'high school']
    occupations = ['teacher', 'doctor', 'engineer']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    education_vars = [z3.Int(f'education_{h}') for h in houses]
    occupation_vars = [z3.Int(f'occupation_{h}') for h in houses]
    
    # Define domains for each variable
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(z3.And(education_vars[h-1] >= 0, education_vars[h-1] < len(educations)))
        solver.add(z3.And(occupation_vars[h-1] >= 0, occupation_vars[h-1] < len(occupations)))
    
    # All attributes are distinct within their categories
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(education_vars))
    solver.add(z3.Distinct(occupation_vars))
    
    # Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
    teacher_idx = occupations.index('teacher')
    associate_idx = educations.index('associate')
    
    # Teacher is directly left of associate's degree (same person)
    # This means the teacher has the associate degree, and they're in house h, with associate in house h+1
    for h in [1, 2]:  # Teacher can only be in house 1 or 2 to be left of someone
        solver.add(z3.Implies(
            occupation_vars[h-1] == teacher_idx,
            education_vars[h] == associate_idx  # Person to the right has associate degree
        ))
    
    # Clue 2: The person with an associate's degree and Eric are next to each other.
    eric_idx = names.index('Eric')
    associate_idx = educations.index('associate')
    
    # Create constraints for Eric being adjacent to the person with associate degree
    for h in houses:
        adjacent_houses = []
        if h > 1:  # Has left neighbor
            adjacent_houses.append(h-2)  # index for house h-1
        if h < 3:  # Has right neighbor
            adjacent_houses.append(h)  # index for house h+1
        
        # If Eric is in house h, then associate degree must be in adjacent house
        solver.add(z3.Implies(
            name_vars[h-1] == eric_idx,
            z3.Or([education_vars[adj] == associate_idx for adj in adjacent_houses])
        ))
        
        # If associate degree is in house h, then Eric must be in adjacent house
        solver.add(z3.Implies(
            education_vars[h-1] == associate_idx,
            z3.Or([name_vars[adj] == eric_idx for adj in adjacent_houses])
        ))
    
    # Clue 3: Peter is the person with a high school diploma.
    peter_idx = names.index('Peter')
    high_school_idx = educations.index('high school')
    
    solver.add(name_vars[0] == peter_idx)  # Peter is in house 1
    solver.add(education_vars[0] == high_school_idx)  # House 1 has high school diploma
    
    # Clue 4: The person who is a doctor is the person with a bachelor's degree.
    doctor_idx = occupations.index('doctor')
    bachelor_idx = educations.index('bachelor')
    
    for h in houses:
        solver.add(z3.Implies(
            occupation_vars[h-1] == doctor_idx,
            education_vars[h-1] == bachelor_idx
        ))
        solver.add(z3.Implies(
            education_vars[h-1] == bachelor_idx,
            occupation_vars[h-1] == doctor_idx
        ))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for h in houses:
            name_val = model.eval(name_vars[h-1]).as_long()
            education_val = model.eval(education_vars[h-1]).as_long()
            occupation_val = model.eval(occupation_vars[h-1]).as_long()
            
            solution.append({
                "House": str(h),
                "Name": names[name_val],
                "Education": educations[education_val],
                "Occupation": occupations[occupation_val]
            })
        
        # Create JSON output
        output = {
            "solution": solution
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()