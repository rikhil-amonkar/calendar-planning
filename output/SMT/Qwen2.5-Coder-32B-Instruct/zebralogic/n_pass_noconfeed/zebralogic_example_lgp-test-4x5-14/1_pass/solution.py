from z3 import *

def solve_puzzle():
    # Define domains
    houses = [1, 2, 3, 4]
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    mothers = ['Janelle', 'Holly', 'Aniya', 'Kailyn']
    smoothies = ['watermelon', 'dragonfruit', 'desert', 'cherry']
    heights = ['tall', 'average', 'short', 'very short']
    educations = ['high school', 'associate', 'master', 'bachelor']

    # Create symbolic variables
    name_vars = {h: Int(f'name_{h}') for h in houses}
    mother_vars = {h: Int(f'mother_{h}') for h in houses}
    smoothie_vars = {h: Int(f'smoothie_{h}') for h in houses}
    height_vars = {h: Int(f'height_{h}') for h in houses}
    education_vars = {h: Int(f'education_{h}') for h in houses}

    # Create solver instance
    solver = Solver()

    # Add domain constraints
    for h in houses:
        solver.add(name_vars[h] >= 0, name_vars[h] < len(names))
        solver.add(mother_vars[h] >= 0, mother_vars[h] < len(mothers))
        solver.add(smoothie_vars[h] >= 0, smoothie_vars[h] < len(smoothies))
        solver.add(height_vars[h] >= 0, height_vars[h] < len(heights))
        solver.add(education_vars[h] >= 0, education_vars[h] < len(educations))

    # All values must be unique across houses
    solver.add(Distinct([name_vars[h] for h in houses]))
    solver.add(Distinct([mother_vars[h] for h in houses]))
    solver.add(Distinct([smoothie_vars[h] for h in houses]))
    solver.add(Distinct([height_vars[h] for h in houses]))
    solver.add(Distinct([education_vars[h] for h in houses]))

    # Clue 1
    solver.add(mother_vars[3] == mothers.index('Janelle'))

    # Clue 2
    solver.add(smoothie_vars[h] == smoothies.index('desert') == education_vars[h] == educations.index('master') for h in houses)

    # Clue 3
    solver.add(smoothie_vars[1] != smoothies.index('desert'))

    # Clue 4
    for i in range(len(houses) - 1):
        solver.add(Or(height_vars[houses[i]] != heights.index('very short'), education_vars[houses[i + 1]] != educations.index('high school')))

    # Clue 5
    solver.add(Or(And(name_vars[h] == names.index('Eric'), smoothie_vars[h + 1] == smoothies.index('cherry')),
                 And(name_vars[h + 1] == names.index('Eric'), smoothie_vars[h] == smoothies.index('cherry'))) for h in range(len(houses) - 1))

    # Clue 6
    solver.add(education_vars[3] != educations.index('high school'))

    # Clue 7
    solver.add(mother_vars[h] == mothers.index('Kailyn') == education_vars[h] == educations.index('associate') for h in houses)

    # Clue 8
    solver.add(smoothie_vars[h] == smoothies.index('cherry') == mother_vars[h] == mothers.index('Aniya') for h in houses)

    # Clue 9
    solver.add(height_vars[h] == heights.index('tall') == mother_vars[h] == mothers.index('Janelle') for h in houses)

    # Clue 10
    for i in range(len(houses) - 1):
        solver.add(Or(height_vars[houses[i]] != heights.index('average'), name_vars[houses[i + 1]] == names.index('Arnold')))

    # Clue 11
    for i in range(len(houses) - 1):
        solver.add(Or(smoothie_vars[houses[i]] != smoothies.index('dragonfruit'), height_vars[houses[i + 1]] == heights.index('short')))

    # Clue 12
    solver.add(name_vars[h] == names.index('Alice') == height_vars[h] == heights.index('tall') for h in houses)

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                "rows": []
            }
        }
        for h in houses:
            name = names[model[name_vars[h]].as_long()]
            mother = mothers[model[mother_vars[h]].as_long()]
            smoothie = smoothies[model[smoothie_vars[h]].as_long()]
            height = heights[model[height_vars[h]].as_long()]
            education = educations[model[education_vars[h]].as_long()]
            solution["solution"]["rows"].append([str(h), name, mother, smoothie, height, education])
        return solution
    else:
        return None

import json
print(json.dumps(solve_puzzle(), indent=2))