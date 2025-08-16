from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3, 4, 5]
names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold']
birthdays = ['mar', 'april', 'sept', 'feb', 'jan']
mothers = ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya']
occupations = ['engineer', 'doctor', 'lawyer', 'artist', 'teacher']
hair_colors = ['red', 'blonde', 'black', 'gray', 'brown']

# Create dictionaries to map variables to their respective domains
name_vars = {house: Int(f'name_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}
mother_vars = {house: Int(f'mother_{house}') for house in houses}
occupation_vars = {house: Int(f'occupation_{house}') for house in houses}
hair_color_vars = {house: Int(f'hair_color_{house}') for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([birthday_vars[house] for house in houses]))
solver.add(Distinct([mother_vars[house] for house in houses]))
solver.add(Distinct([occupation_vars[house] for house in houses]))
solver.add(Distinct([hair_color_vars[house] for house in houses]))

# Map indices to actual values
name_map = {i: name for i, name in enumerate(names)}
birthday_map = {i: birthday for i, birthday in enumerate(birthdays)}
mother_map = {i: mother for i, mother in enumerate(mothers)}
occupation_map = {i: occupation for i, occupation in enumerate(occupations)}
hair_color_map = {i: hair_color for i, hair_color in enumerate(hair_colors)}

# Add clues as constraints
# Clue 1
solver.add(birthday_vars[5] == birthdays.index('mar'))
# Clue 2
solver.add(birthday_vars[1] == birthdays.index('feb'))
# Clue 3
solver.add(name_vars[eric_house] == names.index('Eric') for eric_house in houses if occupation_vars[eric_house] == occupations.index('doctor'))
# Clue 4
solver.add(mother_vars[3] == mothers.index('Janelle'))
# Clue 5 & 6
solver.add(hair_color_vars[4] == hair_colors.index('brown'))
solver.add(occupation_vars[4] == occupations.index('artist'))
# Clue 7
solver.add(Or([And(mother_vars[left_house] == mothers.index('Penny'), hair_color_vars[right_house] == hair_colors.index('black')) for left_house in range(1, 5) for right_house in range(left_house + 1, 6)]))
# Clue 8
solver.add(name_vars[peter_house] == names.index('Peter') for peter_house in houses if hair_color_vars[peter_house] == hair_colors.index('black'))
# Clue 9
solver.add(Or([And(hair_color_vars[teacher_house] == hair_colors.index('gray'), occupation_vars[teacher_house] == occupations.index('teacher')) for teacher_house in houses]))
# Clue 10
solver.add(name_vars[alice_house] == names.index('Alice') for alice_house in houses if mother_vars[alice_house] == mothers.index('Kailyn'))
# Clue 11
solver.add(Or([And(birthday_vars[left_house] == birthdays.index('sept'), name_vars[right_house] == names.index('Arnold')) for left_house in range(1, 5) for right_house in range(left_house + 1, 6)]))
# Clue 12
solver.add(Or([And(birthday_vars[jan_house] == birthdays.index('jan'), hair_color_vars[jan_house] == hair_colors.index('brown')) for jan_house in houses]))
# Clue 13
solver.add(name_vars[arnold_house] == names.index('Arnold') for arnold_house in houses if hair_color_vars[arnold_house] == hair_colors.index('blonde'))
# Clue 14
solver.add(Or([And(mother_vars[black_hair_mother_house] == mothers.index('Holly'), hair_color_vars[black_hair_mother_house] == hair_colors.index('black')) for black_hair_mother_house in houses]))
# Clue 15
solver.add(name_vars[peter_house] == names.index('Peter') for peter_house in houses if occupation_vars[peter_house] == occupations.index('lawyer'))
# Clue 16
solver.add(Or([And(birthday_vars[left_house] == birthdays.index('sept'), mother_vars[right_house] == mothers.index('Kailyn')) for left_house in range(1, 5) for right_house in range(left_house + 1, 6)]))
# Clue 17
solver.add(name_vars[alice_house] == names.index('Alice') for alice_house in houses if hair_color_vars[alice_house] == hair_colors.index('gray'))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": []
        }
    }
    for house in houses:
        name = name_map[model[name_vars[house]].as_long()]
        birthday = birthday_map[model[birthday_vars[house]].as_long()]
        mother = mother_map[model[mother_vars[house]].as_long()]
        occupation = occupation_map[model[occupation_vars[house]].as_long()]
        hair_color = hair_color_map[model[hair_color_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, birthday, mother, occupation, hair_color])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")