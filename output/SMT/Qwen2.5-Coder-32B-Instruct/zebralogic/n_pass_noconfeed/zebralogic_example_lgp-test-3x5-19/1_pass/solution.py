from z3 import *

def solve_puzzle():
    # Create variables
    names = ['Arnold', 'Peter', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    educations = ['associate', 'high school', 'bachelor']
    smoothies = ['desert', 'cherry', 'watermelon']
    hobbies = ['gardening', 'cooking', 'photography']

    # Create symbolic variables for each attribute in each house
    house_vars = {}
    for house in range(1, 4):
        house_vars[house] = {
            'name': Int(f'name_{house}'),
            'occupation': Int(f'occupation_{house}'),
            'education': Int(f'education_{house}'),
            'smoothie': Int(f'smoothie_{house}'),
            'hobby': Int(f'hobby_{house}')
        }

    # Create a solver instance
    solver = Solver()

    # Define domains for each variable
    for house in range(1, 4):
        solver.add(house_vars[house]['name'] >= 0)
        solver.add(house_vars[house]['name'] <= 2)
        solver.add(house_vars[house]['occupation'] >= 0)
        solver.add(house_vars[house]['occupation'] <= 2)
        solver.add(house_vars[house]['education'] >= 0)
        solver.add(house_vars[house]['education'] <= 2)
        solver.add(house_vars[house]['smoothie'] >= 0)
        solver.add(house_vars[house]['smoothie'] <= 2)
        solver.add(house_vars[house]['hobby'] >= 0)
        solver.add(house_vars[house]['hobby'] <= 2)

    # All attributes are unique across houses
    for attr in ['name', 'occupation', 'education', 'smoothie', 'hobby']:
        solver.add(Distinct([house_vars[house][attr] for house in range(1, 4)]))

    # Add clues as constraints
    # Clue 1: The Desert smoothie lover is the person who is a doctor.
    solver.add(Implies(house_vars[house]['smoothie'] == smoothies.index('desert'), house_vars[house]['occupation'] == occupations.index('doctor')) for house in range(1, 4))
    # Clue 2: Arnold is not in the third house.
    solver.add(house_vars[3]['name'] != names.index('Arnold'))
    # Clue 3: The person who likes Cherry smoothies is somewhere to the right of Peter.
    solver.add(Or(And(house_vars[1]['name'] == names.index('Peter'), house_vars[2]['smoothie'] == smoothies.index('cherry')),
                   And(house_vars[1]['name'] == names.index('Peter'), house_vars[3]['smoothie'] == smoothies.index('cherry')),
                   And(house_vars[2]['name'] == names.index('Peter'), house_vars[3]['smoothie'] == smoothies.index('cherry'))))
    # Clue 4: The person who loves cooking is in the second house.
    solver.add(house_vars[2]['hobby'] == hobbies.index('cooking'))
    # Clue 5: The person who loves cooking is Peter.
    solver.add(house_vars[2]['name'] == names.index('Peter'))
    # Clue 6: The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
    solver.add(Or(And(house_vars[1]['hobby'] == hobbies.index('gardening'), house_vars[2]['education'] == educations.index('associate')),
                   And(house_vars[1]['hobby'] == hobbies.index('gardening'), house_vars[3]['education'] == educations.index('associate')),
                   And(house_vars[2]['hobby'] == hobbies.index('gardening'), house_vars[3]['education'] == educations.index('associate'))))
    # Clue 7: The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
    solver.add(Or(And(house_vars[1]['smoothie'] == smoothies.index('desert'), house_vars[2]['education'] == educations.index('bachelor')),
                   And(house_vars[1]['smoothie'] == smoothies.index('desert'), house_vars[3]['education'] == educations.index('bachelor')),
                   And(house_vars[2]['smoothie'] == smoothies.index('desert'), house_vars[3]['education'] == educations.index('bachelor'))))
    # Clue 8: The person who loves cooking is the person who is a doctor.
    solver.add(house_vars[2]['occupation'] == occupations.index('doctor'))
    # Clue 9: The photography enthusiast is the person who is a teacher.
    solver.add(Implies(house_vars[house]['hobby'] == hobbies.index('photography'), house_vars[house]['occupation'] == occupations.index('teacher')) for house in range(1, 4))

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                "rows": []
            }
        }
        for house in range(1, 4):
            name = names[model.evaluate(house_vars[house]['name']).as_long()]
            occupation = occupations[model.evaluate(house_vars[house]['occupation']).as_long()]
            education = educations[model.evaluate(house_vars[house]['education']).as_long()]
            smoothie = smoothies[model.evaluate(house_vars[house]['smoothie']).as_long()]
            hobby = hobbies[model.evaluate(house_vars[house]['hobby']).as_long()]
            solution["solution"]["rows"].append([str(house), name, occupation, education, smoothie, hobby])
        return solution
    else:
        return None

import json
print(json.dumps(solve_puzzle(), indent=2))