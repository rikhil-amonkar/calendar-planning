from z3 import *

# Define the variables
houses = [Int(f'house_{i}') for i in range(1, 6)]
names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']

# Create dictionaries to map names, nationalities, vacations, educations, and occupations to integer variables
name_vars = {name: Int(name) for name in names}
nationality_vars = {nat: Int(nat) for nat in nationalities}
vacation_vars = {vac: Int(vac) for vac in vacations}
education_vars = {edu: Int(edu) for edu in educations}
occupation_vars = {occ: Int(occ) for occ in occupations}

# Create a solver instance
solver = Solver()

# Add constraints for each variable to be between 1 and 5
for var_dict in [name_vars, nationality_vars, vacation_vars, education_vars, occupation_vars]:
    for var in var_dict.values():
        solver.add(And(var >= 1, var <= 5))

# Add constraints for uniqueness within each category
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(nationality_vars.values())))
solver.add(Distinct(list(vacation_vars.values())))
solver.add(Distinct(list(education_vars.values())))
solver.add(Distinct(list(occupation_vars.values())))

# Add clues as constraints
# 1. The person who likes going on cruises is the person who is a lawyer.
solver.add(vacation_vars['cruise'] == occupation_vars['lawyer'])

# 2. The person who loves beach vacations is directly left of Arnold.
solver.add(vacation_vars['beach'] + 1 == name_vars['Arnold'])

# 3. The person with a doctorate is somewhere to the left of Bob.
solver.add(education_vars['doctorate'] < name_vars['Bob'])

# 4. The person with an associate's degree is the person who likes going on cruises.
solver.add(education_vars['associate'] == vacation_vars['cruise'])

# 5. Peter is not in the first house.
solver.add(name_vars['Peter'] != 1)

# 6. The person who is an artist is Peter.
solver.add(occupation_vars['artist'] == name_vars['Peter'])

# 7. The person who enjoys camping trips is the person with a master's degree.
solver.add(vacation_vars['camping'] == education_vars['master'])

# 8. The Dane is somewhere to the right of the person who is a doctor.
solver.add(nationality_vars['dane'] > occupation_vars['doctor'])

# 9. The person with an associate's degree is directly left of the person who is an engineer.
solver.add(education_vars['associate'] + 1 == occupation_vars['engineer'])

# 10. The person who enjoys camping trips is the British person.
solver.add(vacation_vars['camping'] == nationality_vars['brit'])

# 11. The Norwegian and the person with a bachelor's degree are next to each other.
solver.add(Or(
    And(nationality_vars['norwegian'] + 1 == education_vars['bachelor']),
    And(nationality_vars['norwegian'] - 1 == education_vars['bachelor'])
))

# 12. The person who is an artist is the Swedish person.
solver.add(occupation_vars['artist'] == nationality_vars['swede'])

# 13. Bob is not in the fourth house.
solver.add(name_vars['Bob'] != 4)

# 14. The person who enjoys camping trips is Eric.
solver.add(vacation_vars['camping'] == name_vars['Eric'])

# 15. Alice is the German.
solver.add(name_vars['Alice'] == nationality_vars['german'])

# 16. The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
solver.add(vacation_vars['beach'] < vacation_vars['city'])

# 17. The person who enjoys mountain retreats is in the fifth house.
solver.add(vacation_vars['mountain'] == 5)

# 18. The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
solver.add(vacation_vars['cruise'] > vacation_vars['beach'])

# 19. The person with a bachelor's degree is in the third house.
solver.add(education_vars['bachelor'] == 3)

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    # Create a list to store the results
    result = []
    for house in range(1, 6):
        name = next(name for name, var in name_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        nationality = next(nat for nat, var in nationality_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        vacation = next(vac for vac, var in vacation_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        education = next(edu for edu, var in education_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        occupation = next(occ for occ, var in occupation_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        result.append([str(house), name, nationality, vacation, education, occupation])
    
    # Print the result in JSON format
    print({
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": result
        }
    })
else:
    print("No solution found")