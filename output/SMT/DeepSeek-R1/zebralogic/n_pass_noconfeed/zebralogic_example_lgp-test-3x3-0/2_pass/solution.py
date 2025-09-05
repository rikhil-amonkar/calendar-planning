import json
from z3 import *

def main():
    solver = Solver()

    # Define attributes
    names = ['Peter', 'Eric', 'Arnold']
    educations = ['bachelor', 'associate', 'high_school']
    occupations = ['teacher', 'doctor', 'engineer']

    # Create Z3 constants for attributes
    Peter, Eric, Arnold = Strings('Peter Eric Arnold')
    bachelor, associate, high_school = Strings('bachelor associate high_school')
    teacher, doctor, engineer = Strings('teacher doctor engineer')

    # Create lists for house attributes
    house_names = [String(f'house{i}_name') for i in range(1, 4)]
    house_educations = [String(f'house{i}_edu') for i in range(1, 4)]
    house_occupations = [String(f'house{i}_occ') for i in range(1, 4)]

    # Add constraints for each house's attributes
    for i in range(3):
        solver.add(Or(house_names[i] == Peter, house_names[i] == Eric, house_names[i] == Arnold))
        solver.add(Or(house_educations[i] == bachelor, house_educations[i] == associate, house_educations[i] == high_school))
        solver.add(Or(house_occupations[i] == teacher, house_occupations[i] == doctor, house_occupations[i] == engineer))

    # Distinct constraints
    solver.add(Distinct(house_names))
    solver.add(Distinct(house_educations))
    solver.add(Distinct(house_occupations))

    # Clue 1: Teacher directly left of associate's degree
    solver.add(Or(
        And(house_occupations[0] == teacher, house_educations[1] == associate),
        And(house_occupations[1] == teacher, house_educations[2] == associate)
    ))

    # Clue 2: Associate's degree and Eric are adjacent
    for i in range(3):
        for j in [i-1, i+1]:
            if 0 <= j < 3:
                solver.add(Implies(house_educations[i] == associate, house_names[j] == Eric))

    # Clue 3: Peter has high school diploma
    for i in range(3):
        solver.add(Implies(house_names[i] == Peter, house_educations[i] == high_school))

    # Clue 4: Doctor has bachelor's degree
    for i in range(3):
        solver.add(Implies(house_occupations[i] == doctor, house_educations[i] == bachelor))

    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in range(3):
            name_val = model.eval(house_names[i])
            edu_val = model.eval(house_educations[i])
            occ_val = model.eval(house_occupations[i])
            rows.append([str(i+1), str(name_val), str(edu_val), str(occ_val)])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Education", "Occupation"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()