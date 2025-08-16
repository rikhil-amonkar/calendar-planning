import json
from z3 import *

# Define EnumSorts
name_enum, (Arnold, Peter, Eric) = EnumSort('Name', ['Arnold', 'Peter', 'Eric'])
occupation_enum, (doctor, teacher, engineer) = EnumSort('Occupation', ['doctor', 'teacher', 'engineer'])
education_enum, (associate, high_school, bachelor) = EnumSort('Education', ['associate', 'high school', 'bachelor'])
smoothie_enum, (desert, cherry, watermelon) = EnumSort('Smoothie', ['desert', 'cherry', 'watermelon'])
hobby_enum, (gardening, cooking, photography) = EnumSort('Hobby', ['gardening', 'cooking', 'photography'])

# Create variables for each house (1, 2, 3)
names = [Const(f'name_{i}', name_enum) for i in range(1, 4)]
occupations = [Const(f'occupation_{i}', occupation_enum) for i in range(1, 4)]
educations = [Const(f'education_{i}', education_enum) for i in range(1, 4)]
smoothies = [Const(f'smoothie_{i}', smoothie_enum) for i in range(1, 4)]
hobbies = [Const(f'hobby_{i}', hobby_enum) for i in range(1, 4)]

solver = Solver()

# Add distinct constraints for each category
solver.add(Distinct(names))
solver.add(Distinct(occupations))
solver.add(Distinct(educations))
solver.add(Distinct(smoothies))
solver.add(Distinct(hobbies))

# Clue 2: Arnold is not in third house
solver.add(names[2] != Arnold)

# Clue 4 and 5: Peter is in house 2, hobby is cooking
solver.add(names[1] == Peter)
solver.add(hobbies[1] == cooking)

# Clue 8: cooking lover is doctor
solver.add(occupations[1] == doctor)

# Clue 1: Desert lover is doctor (so in house 2)
solver.add(smoothies[1] == desert)

# Clue 3: Cherry is in house 3
solver.add(smoothies[2] == cherry)

# Clue 7: bachelor in house 3
solver.add(educations[2] == bachelor)

# Clue 9: photography implies teacher
for i in range(3):
    solver.add(Implies(hobbies[i] == photography, occupations[i] == teacher))

# Clue 6: associate is to the right of gardening
gardening_house = Int('gardening_house')
associate_house = Int('associate_house')

solver.add(Or(
    And(hobbies[0] == gardening, gardening_house == 1),
    And(hobbies[1] == gardening, gardening_house == 2),
    And(hobbies[2] == gardening, gardening_house == 3)
))

solver.add(Or(
    And(educations[0] == associate, associate_house == 1),
    And(educations[1] == associate, associate_house == 2),
))

solver.add(associate_house > gardening_house)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Now extract the data for each house
    solution = []
    for i in range(3):
        house_num = i + 1
        name = model.eval(names[i])
        occupation = model.eval(occupations[i])
        education = model.eval(educations[i])
        smoothie = model.eval(smoothies[i])
        hobby = model.eval(hobbies[i])
        # Convert to strings
        solution.append([
            str(house_num),
            str(name),
            str(occupation),
            str(education),
            str(smoothie),
            str(hobby)
        ])
    # Now format into the required JSON structure
    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")