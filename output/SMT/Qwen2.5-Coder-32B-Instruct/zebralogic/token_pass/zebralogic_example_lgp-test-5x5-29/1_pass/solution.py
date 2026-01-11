from z3 import *

# Define the number of houses
num_houses = 5

# Create integer variables for each attribute in each house
names = [Int(f'name_{i}') for i in range(num_houses)]
nationalities = [Int(f'nationality_{i}') for i in range(num_houses)]
vacations = [Int(f'vacation_{i}') for i in range(num_houses)]
educations = [Int(f'education_{i}') for i in range(num_houses)]
occupations = [Int(f'occupation_{i}') for i in range(num_houses)]

# Define the possible values for each attribute
names_values = {'Eric': 0, 'Peter': 1, 'Alice': 2, 'Bob': 3, 'Arnold': 4}
nationalities_values = {'norwegian': 0, 'brit': 1, 'swede': 2, 'dane': 3, 'german': 4}
vacations_values = {'cruise': 0, 'mountain': 1, 'camping': 2, 'beach': 3, 'city': 4}
educations_values = {'bachelor': 0, 'master': 1, 'associate': 2, 'doctorate': 3, 'high school': 4}
occupations_values = {'artist': 0, 'doctor': 1, 'engineer': 2, 'teacher': 3, 'lawyer': 4}

# Create a solver instance
solver = Solver()

# Add constraints for unique values in each attribute across houses
solver.add(Distinct(names))
solver.add(Distinct(nationalities))
solver.add(Distinct(vacations))
solver.add(Distinct(educations))
solver.add(Distinct(occupations))

# Add constraints based on the clues
# 1. The person who likes going on cruises is the person who is a lawyer.
solver.add(vacations_values['cruise'] == occupations_values['lawyer'])

# 2. The person who loves beach vacations is directly left of Arnold.
solver.add(vacations_values['beach'] == names[Arnold] - 1)

# 3. The person with a doctorate is somewhere to the left of Bob.
solver.add(educations_values['doctorate'] < names[Bob])

# 4. The person with an associate's degree is the person who likes going on cruises.
solver.add(educations_values['associate'] == vacations_values['cruise'])

# 5. Peter is not in the first house.
solver.add(names[Peter] != 0)

# 6. The person who is an artist is Peter.
solver.add(occupations_values['artist'] == names[Peter])

# 7. The person who enjoys camping trips is the person with a master's degree.
solver.add(vacations_values['camping'] == educations_values['master'])

# 8. The Dane is somewhere to the right of the person who is a doctor.
solver.add(nationalities_values['dane'] > occupations_values['doctor'])

# 9. The person with an associate's degree is directly left of the person who is an engineer.
solver.add(educations_values['associate'] == occupations_values['engineer'] - 1)

# 10. The person who enjoys camping trips is the British person.
solver.add(vacations_values['camping'] == nationalities_values['brit'])

# 11. The Norwegian and the person with a bachelor's degree are next to each other.
solver.add(Or(
    And(nationalities_values['norwegian'] == educations_values['bachelor'] + 1),
    And(nationalities_values['norwegian'] == educations_values['bachelor'] - 1)
))

# 12. The person who is an artist is the Swedish person.
solver.add(occupations_values['artist'] == nationalities_values['swede'])

# 13. Bob is not in the fourth house.
solver.add(names[Bob] != 3)

# 14. The person who enjoys camping trips is Eric.
solver.add(vacations_values['camping'] == names[Eric])

# 15. Alice is the German.
solver.add(names[Alice] == nationalities_values['german'])

# 16. The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
solver.add(vacations_values['beach'] < vacations_values['city'])

# 17. The person who enjoys mountain retreats is in the fifth house.
solver.add(vacations_values['mountain'] == 4)

# 18. The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
solver.add(vacations_values['cruise'] > vacations_values['beach'])

# 19. The person with a bachelor's degree is in the third house.
solver.add(educations_values['bachelor'] == 2)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Map the integer values back to their corresponding attribute names
    def get_value(var_dict, var):
        for key, value in var_dict.items():
            if model.evaluate(var) == value:
                return key
        return None
    
    solution = []
    for i in range(num_houses):
        name = get_value(names_values, names[i])
        nationality = get_value(nationalities_values, nationalities[i])
        vacation = get_value(vacations_values, vacations[i])
        education = get_value(educations_values, educations[i])
        occupation = get_value(occupations_values, occupations[i])
        solution.append([str(i+1), name, nationality, vacation, education, occupation])
    
    # Print the solution in the required format
    print({
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": solution
        }
    })
else:
    print("No solution found")