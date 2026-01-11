from z3 import *

# Define the domains
names = ["Arnold", "Peter", "Eric"]
occupations = ["doctor", "teacher", "engineer"]
educations = ["associate", "high school", "bachelor"]
smoothies = ["desert", "cherry", "watermelon"]
hobbies = ["gardening", "cooking", "photography"]

# Create variables for each house
house_vars = []
for i in range(3):
    name_var = EnumSort('Name%d' % (i+1), names)[0]
    occupation_var = EnumSort('Occupation%d' % (i+1), occupations)[0]
    education_var = EnumSort('Education%d' % (i+1), educations)[0]
    smoothie_var = EnumSort('Smoothie%d' % (i+1), smoothies)[0]
    hobby_var = EnumSort('Hobby%d' % (i+1), hobbies)[0]
    house_vars.append((name_var, occupation_var, education_var, smoothie_var, hobby_var))

# Unpack variables for convenience
(name1, occupation1, education1, smoothie1, hobby1) = house_vars[0]
(name2, occupation2, education2, smoothie2, hobby2) = house_vars[1]
(name3, occupation3, education3, smoothie3, hobby3) = house_vars[2]

# Create a solver instance
solver = Solver()

# Add constraints based on clues
# Clue 1
solver.add(Implies(smoothie1 == smoothies[0], occupation1 == occupations[0]))
solver.add(Implies(smoothie2 == smoothies[0], occupation2 == occupations[0]))
solver.add(Implies(smoothie3 == smoothies[0], occupation3 == occupations[0]))

# Clue 2
solver.add(name3 != names[0])

# Clue 3
solver.add(Implies(name1 == names[1], smoothie1 != smoothies[1]))
solver.add(Implies(name2 == names[1], smoothie2 != smoothies[1]))

# Clue 4
solver.add(hobby2 == hobbies[1])

# Clue 5
solver.add(name2 == names[1])

# Clue 6
solver.add(Implies(hobby1 == hobbies[0], education1 != educations[0]))

# Clue 7
solver.add(Implies(smoothie1 == smoothies[0], education1 != educations[2]))

# Clue 8
solver.add(Implies(hobby2 == hobbies[1], occupation2 == occupations[0]))

# Clue 9
solver.add(Implies(hobby1 == hobbies[2], occupation1 == occupations[1]))
solver.add(Implies(hobby2 == hobbies[2], occupation2 == occupations[1]))
solver.add(Implies(hobby3 == hobbies[2], occupation3 == occupations[1]))

# Ensure uniqueness of each attribute across houses
solver.add(Distinct(name1, name2, name3))
solver.add(Distinct(occupation1, occupation2, occupation3))
solver.add(Distinct(education1, education2, education3))
solver.add(Distinct(smoothie1, smoothie2, smoothie3))
solver.add(Distinct(hobby1, hobby2, hobby3))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
            "rows": [
                ["1", str(model[name1]), str(model[occupation1]), str(model[education1]), str(model[smoothie1]), str(model[hobby1])],
                ["2", str(model[name2]), str(model[occupation2]), str(model[education2]), str(model[smoothie2]), str(model[hobby2])],
                ["3", str(model[name3]), str(model[occupation3]), str(model[education3]), str(model[smoothie3]), str(model[hobby3])]
            ]
        }
    }
    print(result)
else:
    print("No solution found")