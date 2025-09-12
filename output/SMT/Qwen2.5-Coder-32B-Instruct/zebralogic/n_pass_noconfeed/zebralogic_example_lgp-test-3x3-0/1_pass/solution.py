from z3 import *

# Create Solver instance
solver = Solver()

# Define variables
names = ['Peter', 'Eric', 'Arnold']
educations = ['bachelor', 'associate', 'high school']
occupations = ['teacher', 'doctor', 'engineer']
houses = [1, 2, 3]

# Declare variables for each house
house_name = {h: Int(f'house_{h}_name') for h in houses}
house_education = {h: Int(f'house_{h}_education') for h in houses}
house_occupation = {h: Int(f'house_{h}_occupation') for h in houses}

# Add constraints for unique values within each category
solver.add(Distinct([house_name[h] for h in houses]))
solver.add(Distinct([house_education[h] for h in houses]))
solver.add(Distinct([house_occupation[h] for h in houses]))

# Map string values to integer codes
name_map = {name: i for i, name in enumerate(names)}
education_map = {edu: i for i, edu in enumerate(educations)}
occupation_map = {occ: i for i, occ in enumerate(occupations)}

# Add constraints based on clues
# Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
solver.add(house_occupation[1] == occupation_map['teacher'] & house_education[2] == education_map['associate'])
solver.add(Or(
    house_occupation[1] == occupation_map['teacher'] & house_education[2] == education_map['associate'],
    house_occupation[2] == occupation_map['teacher'] & house_education[3] == education_map['associate']
))

# Clue 2: The person with an associate's degree and Eric are next to each other.
solver.add(Or(
    house_education[1] == education_map['associate'] & house_name[2] == name_map['Eric'],
    house_name[1] == name_map['Eric'] & house_education[2] == education_map['associate'],
    house_education[2] == education_map['associate'] & house_name[3] == name_map['Eric'],
    house_name[2] == name_map['Eric'] & house_education[3] == education_map['associate']
))

# Clue 3: Peter is the person with a high school diploma.
solver.add(house_name[h] == name_map['Peter'] & house_education[h] == education_map['high school'] for h in houses)

# Clue 4: The person who is a doctor is the person with a bachelor's degree.
solver.add(house_occupation[h] == occupation_map['doctor'] & house_education[h] == education_map['bachelor'] for h in houses)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": []
        }
    }
    for h in houses:
        name = names[model.eval(house_name[h]).as_long()]
        education = educations[model.eval(house_education[h]).as_long()]
        occupation = occupations[model.eval(house_occupation[h]).as_long()]
        solution["solution"]["rows"].append([str(h), name, education, occupation])
    import json
    print(json.dumps(solution))
else:
    print("No solution found")