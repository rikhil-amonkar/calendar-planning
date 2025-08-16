from z3 import *

# Create Solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3]
names = ['Arnold', 'Peter', 'Eric']
occupations = ['doctor', 'teacher', 'engineer']
educations = ['associate', 'high school', 'bachelor']
smoothies = ['desert', 'cherry', 'watermelon']
hobbies = ['gardening', 'cooking', 'photography']

# Create dictionaries to map variables to Z3 variables
name_vars = {name: Int(f'name_{name}') for name in names}
occupation_vars = {occupation: Int(f'occupation_{occupation}') for occupation in occupations}
education_vars = {education: Int(f'education_{education}') for education in educations}
smoothie_vars = {smoothie: Int(f'smoothie_{smoothie}') for smoothie in smoothies}
hobby_vars = {hobby: Int(f'hobby_{hobby}') for hobby in hobbies}

# Add constraints for unique values per category
solver.add(Distinct([name_vars[name] for name in names]))
solver.add(Distinct([occupation_vars[occupation] for occupation in occupations]))
solver.add(Distinct([education_vars[education] for education in educations]))
solver.add(Distinct([smoothie_vars[smoothie] for smoothie in smoothies]))
solver.add(Distinct([hobby_vars[hobby] for hobby in hobbies]))

# Add constraints for each house to have one of each category
for house in houses:
    solver.add(Or([name_vars[name] == house for name in names]))
    solver.add(Or([occupation_vars[occupation] == house for occupation in occupations]))
    solver.add(Or([education_vars[education] == house for education in educations]))
    solver.add(Or([smoothie_vars[smoothie] == house for smoothie in smoothies]))
    solver.add(Or([hobby_vars[hobby] == house for hobby in hobbies]))

# Apply clues
# Clue 1: The Desert smoothie lover is the person who is a doctor.
solver.add(smoothie_vars['desert'] == occupation_vars['doctor'])

# Clue 2: Arnold is not in the third house.
solver.add(name_vars['Arnold'] != 3)

# Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
solver.add(smoothie_vars['cherry'] > name_vars['Peter'])

# Clue 4: The person who loves cooking is in the second house.
solver.add(hobby_vars['cooking'] == 2)

# Clue 5: The person who loves cooking is Peter.
solver.add(name_vars['Peter'] == hobby_vars['cooking'])

# Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
solver.add(education_vars['associate'] > hobby_vars['gardening'])

# Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
solver.add(education_vars['bachelor'] > smoothie_vars['desert'])

# Clue 8: The person who loves cooking is the person who is a doctor.
solver.add(hobby_vars['cooking'] == occupation_vars['doctor'])

# Clue 9: The photography enthusiast is the person who is a teacher.
solver.add(hobby_vars['photography'] == occupation_vars['teacher'])

# Check if the problem is solvable and get the model
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [str(house)]
        for name in names:
            if model.evaluate(name_vars[name]) == house:
                row.append(name)
        for occupation in occupations:
            if model.evaluate(occupation_vars[occupation]) == house:
                row.append(occupation)
        for education in educations:
            if model.evaluate(education_vars[education]) == house:
                row.append(education)
        for smoothie in smoothies:
            if model.evaluate(smoothie_vars[smoothie]) == house:
                row.append(smoothie)
        for hobby in hobbies:
            if model.evaluate(hobby_vars[hobby]) == house:
                row.append(hobby)
        solution["solution"]["rows"].append(row)
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")