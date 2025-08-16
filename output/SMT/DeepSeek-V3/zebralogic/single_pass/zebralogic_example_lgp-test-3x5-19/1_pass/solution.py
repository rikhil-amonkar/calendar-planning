import json
from z3 import *

# Initialize the solver
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define attributes
names = ['Arnold', 'Peter', 'Eric']
occupations = ['doctor', 'teacher', 'engineer']
educations = ['associate', 'high school', 'bachelor']
smoothies = ['desert', 'cherry', 'watermelon']
hobbies = ['gardening', 'cooking', 'photography']

# Create variables for each attribute in each house
name = {house: Int(f'name_{house}') for house in houses}
occupation = {house: Int(f'occupation_{house}') for house in houses}
education = {house: Int(f'education_{house}') for house in houses}
smoothie = {house: Int(f'smoothie_{house}') for house in houses}
hobby = {house: Int(f'hobby_{house}') for house in houses}

# Add constraints for each attribute to be within their respective ranges
for house in houses:
    s.add(name[house] >= 0, name[house] < len(names))
    s.add(occupation[house] >= 0, occupation[house] < len(occupations))
    s.add(education[house] >= 0, education[house] < len(educations))
    s.add(smoothie[house] >= 0, smoothie[house] < len(smoothies))
    s.add(hobby[house] >= 0, hobby[house] < len(hobbies))

# All attributes in each category must be distinct per house
s.add(Distinct([name[house] for house in houses]))
s.add(Distinct([occupation[house] for house in houses]))
s.add(Distinct([education[house] for house in houses]))
s.add(Distinct([smoothie[house] for house in houses]))
s.add(Distinct([hobby[house] for house in houses]))

# Clue 2: Arnold is not in the third house.
# Arnold is names[0], so name[3] != 0
s.add(name[3] != 0)

# Clue 4: The person who loves cooking is in the second house.
# cooking is hobbies[1], so hobby[2] == 1
s.add(hobby[2] == 1)

# Clue 5: The person who loves cooking is Peter.
# Peter is names[1], so name of house where hobby is cooking (house 2) is Peter.
s.add(name[2] == 1)

# Clue 8: The person who loves cooking is the person who is a doctor.
# So occupation of house 2 is doctor (occupations[0])
s.add(occupation[2] == 0)

# Clue 1: The Desert smoothie lover is the person who is a doctor.
# So smoothie of house 2 is desert (smoothies[0])
s.add(smoothie[2] == 0)

# Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
# Peter is in house 2, so cherry (smoothies[1]) must be in a house with number > 2. So house 3.
s.add(smoothie[3] == 1)

# Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
# Desert smoothie lover is in house 2, so bachelor (educations[2]) must be in house 3.
s.add(education[3] == 2)

# Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
# So gardening is left of associate. Gardening could be in 1, associate in 2 or 3, or gardening in 2, associate in 3.
# But house 2's hobby is cooking, so gardening must be in 1, associate in 2 or 3.
# But education in 3 is bachelor, so associate must be in 2.
s.add(education[2] == 0)
# So gardening must be in 1.
s.add(hobby[1] == 0)

# Clue 9: The photography enthusiast is the person who is a teacher.
# So for any house, if hobby is photography (hobbies[2]), then occupation is teacher (occupations[1]).
for house in houses:
    s.add(Implies(hobby[house] == 2, occupation[house] == 1))

# Now, let's assign the remaining attributes.
# Name assignments: house 2 is Peter (1). Arnold is not in 3, so Arnold is in 1, Eric in 3.
s.add(name[1] == 0)
s.add(name[3] == 2)

# Occupation assignments: house 2 is doctor (0). The remaining occupations are teacher and engineer.
# From clue 9, photography is teacher. So hobby 2 is cooking, so photography must be in 1 or 3.
# Hobby in 1 is gardening, so photography is in 3.
s.add(hobby[3] == 2)
# So occupation in 3 is teacher (from clue 9).
s.add(occupation[3] == 1)
# Thus, occupation in 1 is engineer.
s.add(occupation[1] == 2)

# Education assignments: house 2 is associate (0), house 3 is bachelor (2), so house 1 is high school (1).
s.add(education[1] == 1)

# Smoothie assignments: house 2 is desert (0), house 3 is cherry (1), so house 1 is watermelon (2).
s.add(smoothie[1] == 2)

# Hobby assignments: house 1 is gardening (0), house 2 is cooking (1), house 3 is photography (2).

# Check if the model is satisfiable
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
            "rows": []
        }
    }
    for house in sorted(houses):
        row = [str(house)]
        # Name
        name_val = model.eval(name[house]).as_long()
        row.append(names[name_val])
        # Occupation
        occ_val = model.eval(occupation[house]).as_long()
        row.append(occupations[occ_val])
        # Education
        edu_val = model.eval(education[house]).as_long()
        row.append(educations[edu_val])
        # Smoothie
        sm_val = model.eval(smoothie[house]).as_long()
        row.append(smoothies[sm_val])
        # Hobby
        hob_val = model.eval(hobby[house]).as_long()
        row.append(hobbies[hob_val])
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")