from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
names = ['Peter', 'Eric', 'Arnold']
educations = ['bachelor', 'associate', 'high school']
occupations = ['teacher', 'doctor', 'engineer']

# Create symbolic variables for each house
house1_name = EnumSort('house1_name', names)[0]
house2_name = EnumSort('house2_name', names)[0]
house3_name = EnumSort('house3_name', names)[0]

house1_education = EnumSort('house1_education', educations)[0]
house2_education = EnumSort('house2_education', educations)[0]
house3_education = EnumSort('house3_education', educations)[0]

house1_occupation = EnumSort('house1_occupation', occupations)[0]
house2_occupation = EnumSort('house2_occupation', occupations)[0]
house3_occupation = EnumSort('house3_occupation', occupations)[0]

# Add constraints
# Each person has a unique name, education, and occupation
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_education, house2_education, house3_education))
solver.add(Distinct(house1_occupation, house2_occupation, house3_occupation))

# Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
solver.add(Or(
    And(house1_occupation == 'teacher', house2_education == 'associate'),
    And(house2_occupation == 'teacher', house3_education == 'associate')
))

# Clue 2: The person with an associate's degree and Eric are next to each other.
solver.add(Or(
    And(house1_education == 'associate', house2_name == 'Eric'),
    And(house2_education == 'associate', Or(house1_name == 'Eric', house3_name == 'Eric')),
    And(house3_education == 'associate', house2_name == 'Eric')
))

# Clue 3: Peter is the person with a high school diploma.
solver.add(house1_name == 'Peter' ==>
           house1_education == 'high school')
solver.add(house2_name == 'Peter' ==>
           house2_education == 'high school')
solver.add(house3_name == 'Peter' ==>
           house3_education == 'high school')

# Clue 4: The person who is a doctor is the person with a bachelor's degree.
solver.add(Or(
    And(house1_occupation == 'doctor', house1_education == 'bachelor'),
    And(house2_occupation == 'doctor', house2_education == 'bachelor'),
    And(house3_occupation == 'doctor', house3_education == 'bachelor')
))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": []
        }
    }
    
    for i, (name_var, education_var, occupation_var) in enumerate([
        (house1_name, house1_education, house1_occupation),
        (house2_name, house2_education, house2_occupation),
        (house3_name, house3_education, house3_occupation)
    ]):
        name = model[name_var].as_string().split('__')[1]
        education = model[education_var].as_string().split('__')[1]
        occupation = model[occupation_var].as_string().split('__')[1]
        
        solution["solution"]["rows"].append([str(i+1), name, education, occupation])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")