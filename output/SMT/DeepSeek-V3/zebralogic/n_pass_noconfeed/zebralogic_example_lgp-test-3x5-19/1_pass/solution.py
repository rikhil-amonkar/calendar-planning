import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Arnold', 'Peter', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    educations = ['associate', 'high school', 'bachelor']
    smoothies = ['desert', 'cherry', 'watermelon']
    hobbies = ['gardening', 'cooking', 'photography']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    occupation_vars = [z3.Int(f'occupation_{h}') for h in houses]
    education_vars = [z3.Int(f'education_{h}') for h in houses]
    smoothie_vars = [z3.Int(f'smoothie_{h}') for h in houses]
    hobby_vars = [z3.Int(f'hobby_{h}') for h in houses]
    
    # Constraint: all attributes must be within their respective domains
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(z3.And(occupation_vars[h-1] >= 0, occupation_vars[h-1] < len(occupations)))
        solver.add(z3.And(education_vars[h-1] >= 0, education_vars[h-1] < len(educations)))
        solver.add(z3.And(smoothie_vars[h-1] >= 0, smoothie_vars[h-1] < len(smoothies)))
        solver.add(z3.And(hobby_vars[h-1] >= 0, hobby_vars[h-1] < len(hobbies)))
    
    # Constraint: all attributes must have unique values across houses
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(occupation_vars))
    solver.add(z3.Distinct(education_vars))
    solver.add(z3.Distinct(smoothie_vars))
    solver.add(z3.Distinct(hobby_vars))
    
    # Clue 1: The Desert smoothie lover is the person who is a doctor.
    desert_idx = smoothies.index('desert')
    doctor_idx = occupations.index('doctor')
    for h in houses:
        solver.add(z3.Implies(smoothie_vars[h-1] == desert_idx, occupation_vars[h-1] == doctor_idx))
    
    # Clue 2: Arnold is not in the third house.
    arnold_idx = names.index('Arnold')
    solver.add(name_vars[2] != arnold_idx)
    
    # Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
    cherry_idx = smoothies.index('cherry')
    peter_idx = names.index('Peter')
    cherry_right_of_peter = []
    for h_peter in houses:
        for h_cherry in houses:
            if h_cherry > h_peter:
                cherry_right_of_peter.append(z3.And(
                    name_vars[h_peter-1] == peter_idx,
                    smoothie_vars[h_cherry-1] == cherry_idx
                ))
    solver.add(z3.Or(cherry_right_of_peter))
    
    # Clue 4: The person who loves cooking is in the second house.
    cooking_idx = hobbies.index('cooking')
    solver.add(hobby_vars[1] == cooking_idx)
    
    # Clue 5: The person who loves cooking is Peter.
    solver.add(z3.Implies(hobby_vars[1] == cooking_idx, name_vars[1] == peter_idx))
    
    # Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
    associate_idx = educations.index('associate')
    gardening_idx = hobbies.index('gardening')
    associate_right_of_gardening = []
    for h_gardening in houses:
        for h_associate in houses:
            if h_associate > h_gardening:
                associate_right_of_gardening.append(z3.And(
                    hobby_vars[h_gardening-1] == gardening_idx,
                    education_vars[h_associate-1] == associate_idx
                ))
    solver.add(z3.Or(associate_right_of_gardening))
    
    # Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
    bachelor_idx = educations.index('bachelor')
    bachelor_right_of_desert = []
    for h_desert in houses:
        for h_bachelor in houses:
            if h_bachelor > h_desert:
                bachelor_right_of_desert.append(z3.And(
                    smoothie_vars[h_desert-1] == desert_idx,
                    education_vars[h_bachelor-1] == bachelor_idx
                ))
    solver.add(z3.Or(bachelor_right_of_desert))
    
    # Clue 8: The person who loves cooking is the person who is a doctor.
    solver.add(z3.Implies(hobby_vars[1] == cooking_idx, occupation_vars[1] == doctor_idx))
    
    # Clue 9: The photography enthusiast is the person who is a teacher.
    photography_idx = hobbies.index('photography')
    teacher_idx = occupations.index('teacher')
    for h in houses:
        solver.add(z3.Implies(hobby_vars[h-1] == photography_idx, occupation_vars[h-1] == teacher_idx))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for h in houses:
            name_val = model.eval(name_vars[h-1]).as_long()
            occupation_val = model.eval(occupation_vars[h-1]).as_long()
            education_val = model.eval(education_vars[h-1]).as_long()
            smoothie_val = model.eval(smoothie_vars[h-1]).as_long()
            hobby_val = model.eval(hobby_vars[h-1]).as_long()
            
            row = [
                str(h),
                names[name_val],
                occupations[occupation_val],
                educations[education_val],
                smoothies[smoothie_val],
                hobbies[hobby_val]
            ]
            solution.append(row)
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()