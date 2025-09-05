import z3
import json

def main():
    names = ['Arnold', 'Alice', 'Eric', 'Peter']
    hobbies = ['cooking', 'painting', 'photography', 'gardening']
    birthdays = ['april', 'jan', 'sept', 'feb']
    educations = ['master', 'bachelor', 'associate', 'high school']
    smoothies = ['cherry', 'watermelon', 'desert', 'dragonfruit']
    
    NameSort, (Arnold, Alice, Eric, Peter) = z3.EnumSort('Name', names)
    HobbySort, (cooking, painting, photography, gardening) = z3.EnumSort('Hobby', hobbies)
    BirthdaySort, (april, jan, sept, feb) = z3.EnumSort('Birthday', birthdays)
    EducationSort, (master, bachelor, associate, high_school) = z3.EnumSort('Education', educations)
    SmoothieSort, (cherry, watermelon, desert, dragonfruit) = z3.EnumSort('Smoothie', smoothies)
    
    houses = [1, 2, 3, 4]
    name_vars = [z3.Const(f'name_{i}', NameSort) for i in houses]
    hobby_vars = [z3.Const(f'hobby_{i}', HobbySort) for i in houses]
    birthday_vars = [z3.Const(f'birthday_{i}', BirthdaySort) for i in houses]
    education_vars = [z3.Const(f'education_{i}', EducationSort) for i in houses]
    smoothie_vars = [z3.Const(f'smoothie_{i}', SmoothieSort) for i in houses]
    
    solver = z3.Solver()
    
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(hobby_vars))
    solver.add(z3.Distinct(birthday_vars))
    solver.add(z3.Distinct(education_vars))
    solver.add(z3.Distinct(smoothie_vars))
    
    for i in houses:
        solver.add(z3.Implies(smoothie_vars[i-1] == desert, birthday_vars[i-1] == jan))
        solver.add(z3.Implies(birthday_vars[i-1] == jan, smoothie_vars[i-1] == desert))
    
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == Eric, education_vars[i-1] == bachelor))
        solver.add(z3.Implies(education_vars[i-1] == bachelor, name_vars[i-1] == Eric))
    
    for i in houses:
        solver.add(z3.Implies(birthday_vars[i-1] == jan, education_vars[i-1] == bachelor))
        solver.add(z3.Implies(education_vars[i-1] == bachelor, birthday_vars[i-1] == jan))
    
    solver.add(education_vars[2] == high_school)
    
    solver.add(smoothie_vars[2] != watermelon)
    
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == associate, name_vars[i-1] == Arnold))
        solver.add(z3.Implies(name_vars[i-1] == Arnold, education_vars[i-1] == associate))
    
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == master, hobby_vars[i-1] == painting))
        solver.add(z3.Implies(hobby_vars[i-1] == painting, education_vars[i-1] == master))
    
    # Constraint 8: The person who likes the dragonfruit smoothie and the person who has the birthday in sept are two houses apart.
    dragonfruit_sept_pairs = []
    # Consider all pairs of houses that are two apart: (1,3), (3,1), (2,4), (4,2)
    dragonfruit_sept_pairs.append(z3.And(smoothie_vars[0] == dragonfruit, birthday_vars[2] == sept))
    dragonfruit_sept_pairs.append(z3.And(smoothie_vars[2] == dragonfruit, birthday_vars[0] == sept))
    dragonfruit_sept_pairs.append(z3.And(smoothie_vars[1] == dragonfruit, birthday_vars[3] == sept))
    dragonfruit_sept_pairs.append(z3.And(smoothie_vars[3] == dragonfruit, birthday_vars[1] == sept))
    solver.add(z3.Or(dragonfruit_sept_pairs))
    
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == high_school, birthday_vars[i-1] == sept))
        solver.add(z3.Implies(birthday_vars[i-1] == sept, education_vars[i-1] == high_school))
    
    for i in houses:
        solver.add(z3.Implies(hobby_vars[i-1] == cooking, name_vars[i-1] == Alice))
        solver.add(z3.Implies(name_vars[i-1] == Alice, hobby_vars[i-1] == cooking))
    
    # Constraint 11: The person who has the birthday in april and the person who likes gardening are adjacent.
    adjacent_pairs = [(0,1), (1,2), (2,3)]
    april_gardening_constraints = []
    for i, j in adjacent_pairs:
        april_gardening_constraints.append(z3.And(birthday_vars[i] == april, hobby_vars[j] == gardening))
        april_gardening_constraints.append(z3.And(birthday_vars[j] == april, hobby_vars[i] == gardening))
    solver.add(z3.Or(april_gardening_constraints))
    
    for i in houses:
        solver.add(z3.Implies(hobby_vars[i-1] == painting, birthday_vars[i-1] == feb))
        solver.add(z3.Implies(birthday_vars[i-1] == feb, hobby_vars[i-1] == painting))
    
    if solver.check() == z3.sat:
        model = solver.model()
        
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
        
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = get_value(name_vars[i], model, name_mapping)
            hobby_val = get_value(hobby_vars[i], model, hobby_mapping)
            birthday_val = get_value(birthday_vars[i], model, birthday_mapping)
            education_val = get_value(education_vars[i], model, education_mapping)
            smoothie_val = get_value(smoothie_vars[i], model, smoothie_mapping)
            rows.append([house_num, name_val, hobby_val, birthday_val, education_val, smoothie_val])
        
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