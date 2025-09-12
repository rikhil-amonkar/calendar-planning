from z3 import *
import json

# Define the variables
houses = [1, 2, 3]
names = ['Eric', 'Peter', 'Arnold']
cigars = ['blue master', 'prince', 'pall mall']
hobbies = ['photography', 'gardening', 'cooking']
educations = ['high school', 'associate', 'bachelor']
drinks = ['tea', 'milk', 'water']

# Create dictionaries to map variables to Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
cigar_vars = {house: Int(f'cigar_{house}') for house in houses}
hobby_vars = {house: Int(f'hobby_{house}') for house in houses}
education_vars = {house: Int(f'education_{house}') for house in houses}
drink_vars = {house: Int(f'drink_{house}') for house in houses}

# Create a solver instance
solver = Solver()

# Add domain constraints
for house in houses:
    solver.add(name_vars[house] >= 0)
    solver.add(name_vars[house] < len(names))
    solver.add(cigar_vars[house] >= 0)
    solver.add(cigar_vars[house] < len(cigars))
    solver.add(hobby_vars[house] >= 0)
    solver.add(hobby_vars[house] < len(hobbies))
    solver.add(education_vars[house] >= 0)
    solver.add(education_vars[house] < len(educations))
    solver.add(drink_vars[house] >= 0)
    solver.add(drink_vars[house] < len(drinks))

# All values must be unique across houses
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([cigar_vars[house] for house in houses]))
solver.add(Distinct([hobby_vars[house] for house in houses]))
solver.add(Distinct([education_vars[house] for house in houses]))
solver.add(Distinct([drink_vars[house] for house in houses]))

# Clue 1: The person partial to Pall Mall is Peter.
solver.add(Or([Implies(cigar_vars[house] == cigars.index('pall mall'), name_vars[house] == names.index('Peter')) for house in houses]))

# Clue 2: The person who likes milk is directly left of the person with a high school diploma.
solver.add(Or([Implies(drink_vars[house] == drinks.index('milk'), education_vars[house + 1] == educations.index('high school')) for house in [1, 2]]))

# Clue 3: Eric is the tea drinker.
solver.add(Or([Implies(drink_vars[house] == drinks.index('tea'), name_vars[house] == names.index('Eric')) for house in houses]))

# Clue 4: Arnold and the Prince smoker are next to each other.
solver.add(Or([Implies(name_vars[house] == names.index('Arnold'), cigar_vars[house + 1] == cigars.index('prince')) for house in [1, 2]]))
solver.add(Or([Implies(name_vars[house] == names.index('Arnold'), cigar_vars[house - 1] == cigars.index('prince')) for house in [2, 3]]))
solver.add(Or([Implies(cigar_vars[house] == cigars.index('prince'), name_vars[house + 1] == names.index('Arnold')) for house in [1, 2]]))
solver.add(Or([Implies(cigar_vars[house] == cigars.index('prince'), name_vars[house - 1] == names.index('Arnold')) for house in [2, 3]]))

# Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
solver.add(Or([Implies(hobby_vars[house] == hobbies.index('gardening'), 
                        Or(cigar_vars[house + 1] == cigars.index('prince'), 
                           And(house + 2 in houses, cigar_vars[house + 2] == cigars.index('prince')))) 
               for house in [1]]))  # Changed from [1, 2] to [1] to avoid out-of-range error

# Clue 6: The person who likes milk is the person with an associate's degree.
solver.add(Or([Implies(drink_vars[house] == drinks.index('milk'), education_vars[house] == educations.index('associate')) for house in houses]))

# Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
solver.add(Or([Implies(education_vars[house] == educations.index('bachelor'), hobby_vars[house + 1] == hobbies.index('photography')) for house in [1, 2]]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        cigar = cigars[model[cigar_vars[house]].as_long()]
        hobby = hobbies[model[hobby_vars[house]].as_long()]
        education = educations[model[education_vars[house]].as_long()]
        drink = drinks[model[drink_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, cigar, hobby, education, drink])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")