import z3
import json

def main():
    # Define the categories and their possible values
    names = ['Arnold', 'Alice', 'Eric', 'Peter']
    hobbies = ['cooking', 'painting', 'photography', 'gardening']
    birthdays = ['april', 'jan', 'sept', 'feb']
    educations = ['master', 'bachelor', 'associate', 'high school']
    smoothies = ['cherry', 'watermelon', 'desert', 'dragonfruit']
    
    # Create Z3 sorts for each category
    NameSort, (Arnold, Alice, Eric, Peter) = z3.EnumSort('Name', names)
    HobbySort, (cooking, painting, photography, gardening) = z3.EnumSort('Hobby', hobbies)
    BirthdaySort, (april, jan, sept, feb) = z3.EnumSort('Birthday', birthdays)
    EducationSort, (master, bachelor, associate, high_school) = z3.EnumSort('Education', educations)
    SmoothieSort, (cherry, watermelon, desert, dragonfruit) = z3.EnumSort('Smoothie', smoothies)
    
    # Create variables for each house for each category
    houses = [1, 2, 3, 4]
    name_vars = [z3.Const(f'name_{i}', NameSort) for i in houses]
    hobby_vars = [z3.Const(f'hobby_{i}', HobbySort) for i in houses]
    birthday_vars = [z3.Const(f'birthday_{i}', BirthdaySort) for i in houses]
    education_vars = [z3.Const(f'education_{i}', EducationSort) for i in houses]
    smoothie_vars = [z3.Const(f'smoothie_{i}', SmoothieSort) for i in houses]
    
    solver = z3.Solver()
    
    # Add constraint: all attributes are distinct per category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(hobby_vars))
    solver.add(z3.Distinct(birthday_vars))
    solver.add(z3.Distinct(education_vars))
    solver.add(z3.Distinct(smoothie_vars))
    
    # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
    for i in houses:
        solver.add(z3.Implies(smoothie_vars[i-1] == desert, birthday_vars[i-1] == jan))
    
    # Clue 2: Eric is the person with a bachelor's degree.
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == Eric, education_vars[i-1] == bachelor))
    
    # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
    for i in houses:
        solver.add(z3.Implies(birthday_vars[i-1] == jan, education_vars[i-1] == bachelor))
    
    # Clue 4: The person with a high school diploma is in the third house.
    solver.add(education_vars[2] == high_school)
    
    # Clue 5: The Watermelon smoothie lover is not in the third house.
    solver.add(smoothie_vars[2] != watermelon)
    
    # Clue 6: The person with an associate's degree is Arnold.
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == associate, name_vars[i-1] == Arnold))
    
    # Clue 7: The person with a master's degree is the person who paints as a hobby.
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == master, hobby_vars[i-1] == painting))
    
    # Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
    for i in houses:
        for j in houses:
            if abs(i - j) == 2:  # One house between means |i-j| = 2
                solver.add(z3.Or(
                    z3.And(smoothie_vars[i-1] == dragonfruit, birthday_vars[j-1] == sept),
                    z3.And(smoothie_vars[j-1] == dragonfruit, birthday_vars[i-1] == sept)
                ))
    
    # Clue 9: The person with a high school diploma is the person whose birthday is in September.
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == high_school, birthday_vars[i-1] == sept))
    
    # Clue 10: The person who loves cooking is Alice.
    for i in houses:
        solver.add(z3.Implies(hobby_vars[i-1] == cooking, name_vars[i-1] == Alice))
    
    # Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
    for i in range(1, 4):
        solver.add(z3.Or(
            z3.And(birthday_vars[i-1] == april, hobby_vars[i] == gardening),
            z3.And(birthday_vars[i] == april, hobby_vars[i-1] == gardening)
        ))
    # Also check adjacent pairs for house 1-2, 2-3, 3-4
    for i in range(1, 4):
        solver.add(z3.Or(
            z3.And(birthday_vars[i-1] == april, hobby_vars[i] == gardening),
            z3.And(birthday_vars[i] == april, hobby_vars[i-1] == gardening),
            z3.And(birthday_vars[i-1] == april, hobby_vars[i-1] == gardening) # Same house? But note: different attributes so cannot be same
        ))
    # Actually, since each attribute is unique, the april birthday and gardening hobby must be in different houses.
    # So we need adjacent houses only. Let's do it properly:
    adjacent_pairs = [(1,2), (2,3), (3,4)]
    for (a, b) in adjacent_pairs:
        solver.add(z3.Or(
            z3.And(birthday_vars[a-1] == april, hobby_vars[b-1] == gardening),
            z3.And(birthday_vars[b-1] == april, hobby_vars[a-1] == gardening)
        ))
    
    # Clue 12: The person who paints as a hobby is the person whose birthday is in February.
    for i in houses:
        solver.add(z3.Implies(hobby_vars[i-1] == painting, birthday_vars[i-1] == feb))
    
    # Check if the solver is satisfied and get the solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create a mapping from Z3 constants to their string representations
        def get_value(var, model, mapping):
            const = model[var]
            if const is None:
                return None
            for key, value in mapping.items():
                if str(const) == str(value):
                    return key
            return None
        
        name_mapping = {n: eval(n) for n in names}
        hobby_mapping = {h: eval(h) for h in hobbies}
        birthday_mapping = {b: eval(b) for b in birthdays}
        education_mapping = {e: eval(e) for e in educations}
        smoothie_mapping = {s: eval(s) for s in smoothies}
        
        # Prepare the result table
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = get_value(name_vars[i], model, name_mapping)
            hobby_val = get_value(hobby_vars[i], model, hobby_mapping)
            birthday_val = get_value(birthday_vars[i], model, birthday_mapping)
            education_val = get_value(education_vars[i], model, education_mapping)
            smoothie_val = get_value(smoothie_vars[i], model, smoothie_mapping)
            rows.append([house_num, name_val, hobby_val, birthday_val, education_val, smoothie_val])
        
        # Create the JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()