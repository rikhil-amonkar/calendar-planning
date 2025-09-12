import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define attributes
    names = ['Arnold', 'Alice', 'Eric', 'Peter']
    hobbies = ['cooking', 'painting', 'photography', 'gardening']
    birthdays = ['jan', 'feb', 'april', 'sept']
    educations = ['master', 'bachelor', 'associate', 'high school']
    smoothies = ['cherry', 'watermelon', 'desert', 'dragonfruit']
    houses = [1, 2, 3, 4]
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{i}') for i in houses]
    hobby_vars = [z3.Int(f'hobby_{i}') for i in houses]
    birthday_vars = [z3.Int(f'birthday_{i}') for i in houses]
    education_vars = [z3.Int(f'education_{i}') for i in houses]
    smoothie_vars = [z3.Int(f'smoothie_{i}') for i in houses]
    
    # Define domains for each variable
    for i in houses:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(z3.And(hobby_vars[i-1] >= 0, hobby_vars[i-1] < len(hobbies)))
        solver.add(z3.And(birthday_vars[i-1] >= 0, birthday_vars[i-1] < len(birthdays)))
        solver.add(z3.And(education_vars[i-1] >= 0, education_vars[i-1] < len(educations)))
        solver.add(z3.And(smoothie_vars[i-1] >= 0, smoothie_vars[i-1] < len(smoothies)))
    
    # All attributes are distinct per house
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(hobby_vars))
    solver.add(z3.Distinct(birthday_vars))
    solver.add(z3.Distinct(education_vars))
    solver.add(z3.Distinct(smoothie_vars))
    
    # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
    desert_idx = smoothies.index('desert')
    jan_idx = birthdays.index('jan')
    for i in houses:
        solver.add(z3.Implies(smoothie_vars[i-1] == desert_idx, birthday_vars[i-1] == jan_idx))
    
    # Clue 2: Eric is the person with a bachelor's degree.
    eric_idx = names.index('Eric')
    bachelor_idx = educations.index('bachelor')
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == eric_idx, education_vars[i-1] == bachelor_idx))
    
    # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
    for i in houses:
        solver.add(z3.Implies(birthday_vars[i-1] == jan_idx, education_vars[i-1] == bachelor_idx))
    
    # Clue 4: The person with a high school diploma is in the third house.
    hs_idx = educations.index('high school')
    solver.add(education_vars[2] == hs_idx)
    
    # Clue 5: The Watermelon smoothie lover is not in the third house.
    watermelon_idx = smoothies.index('watermelon')
    solver.add(smoothie_vars[2] != watermelon_idx)
    
    # Clue 6: The person with an associate's degree is Arnold.
    associate_idx = educations.index('associate')
    arnold_idx = names.index('Arnold')
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == associate_idx, name_vars[i-1] == arnold_idx))
    
    # Clue 7: The person with a master's degree is the person who paints as a hobby.
    master_idx = educations.index('master')
    painting_idx = hobbies.index('painting')
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == master_idx, hobby_vars[i-1] == painting_idx))
    
    # Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
    dragonfruit_idx = smoothies.index('dragonfruit')
    sept_idx = birthdays.index('sept')
    
    # Create variables for positions
    dragonfruit_pos = z3.Int('dragonfruit_pos')
    sept_pos = z3.Int('sept_pos')
    
    # Constrain positions to be valid house numbers
    solver.add(z3.And(dragonfruit_pos >= 1, dragonfruit_pos <= 4))
    solver.add(z3.And(sept_pos >= 1, sept_pos <= 4))
    
    # Link position variables to actual attributes
    for i in houses:
        solver.add(z3.Implies(smoothie_vars[i-1] == dragonfruit_idx, dragonfruit_pos == i))
        solver.add(z3.Implies(birthday_vars[i-1] == sept_idx, sept_pos == i))
    
    # One house between means |dragonfruit_pos - sept_pos| = 2
    solver.add(z3.Or(
        dragonfruit_pos - sept_pos == 2,
        sept_pos - dragonfruit_pos == 2
    ))
    
    # Clue 9: The person with a high school diploma is the person whose birthday is in September.
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == hs_idx, birthday_vars[i-1] == sept_idx))
    
    # Clue 10: The person who loves cooking is Alice.
    cooking_idx = hobbies.index('cooking')
    alice_idx = names.index('Alice')
    for i in houses:
        solver.add(z3.Implies(hobby_vars[i-1] == cooking_idx, name_vars[i-1] == alice_idx))
    
    # Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
    april_idx = birthdays.index('april')
    gardening_idx = hobbies.index('gardening')
    
    # Create variables for positions
    april_pos = z3.Int('april_pos')
    gardening_pos = z3.Int('gardening_pos')
    
    # Constrain positions to be valid house numbers
    solver.add(z3.And(april_pos >= 1, april_pos <= 4))
    solver.add(z3.And(gardening_pos >= 1, gardening_pos <= 4))
    
    # Link position variables to actual attributes
    for i in houses:
        solver.add(z3.Implies(birthday_vars[i-1] == april_idx, april_pos == i))
        solver.add(z3.Implies(hobby_vars[i-1] == gardening_idx, gardening_pos == i))
    
    # Adjacent means |april_pos - gardening_pos| = 1
    solver.add(z3.Or(
        april_pos - gardening_pos == 1,
        gardening_pos - april_pos == 1
    ))
    
    # Clue 12: The person who paints as a hobby is the person whose birthday is in February.
    feb_idx = birthdays.index('feb')
    for i in houses:
        solver.add(z3.Implies(hobby_vars[i-1] == painting_idx, birthday_vars[i-1] == feb_idx))
    
    # Check if satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract values
        result = []
        for i in houses:
            name_val = model.eval(name_vars[i-1]).as_long()
            hobby_val = model.eval(hobby_vars[i-1]).as_long()
            birthday_val = model.eval(birthday_vars[i-1]).as_long()
            education_val = model.eval(education_vars[i-1]).as_long()
            smoothie_val = model.eval(smoothie_vars[i-1]).as_long()
            
            result.append([
                str(i),
                names[name_val],
                hobbies[hobby_val],
                birthdays[birthday_val],
                educations[education_val],
                smoothies[smoothie_val]
            ])
        
        # Sort by house number
        result.sort(key=lambda x: int(x[0]))
        
        # Create JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                "rows": result
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()