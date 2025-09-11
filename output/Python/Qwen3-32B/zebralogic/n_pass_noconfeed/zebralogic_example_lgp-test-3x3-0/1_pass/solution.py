import itertools
import json

def solve_puzzle():
    names = ['Peter', 'Eric', 'Arnold']
    educations = ['bachelor', 'associate', 'high school']
    occupations = ['teacher', 'doctor', 'engineer']

    for name_perm in itertools.permutations(names):
        for edu_perm in itertools.permutations(educations):
            for occ_perm in itertools.permutations(occupations):
                # Check clue 3: Peter has high school
                peter_has_high = True
                for i in range(3):
                    if name_perm[i] == 'Peter' and edu_perm[i] != 'high school':
                        peter_has_high = False
                        break
                if not peter_has_high:
                    continue

                # Check clue 1: teacher is directly left of associate
                teacher_index = occ_perm.index('teacher')
                associate_index = edu_perm.index('associate')
                if teacher_index + 1 != associate_index:
                    continue

                # Check clue 4: doctor has bachelor's
                doctor_index = occ_perm.index('doctor')
                if edu_perm[doctor_index] != 'bachelor':
                    continue

                # Check clue 2: associate and Eric are adjacent
                associate_index = edu_perm.index('associate')
                eric_index = name_perm.index('Eric')
                if abs(associate_index - eric_index) != 1:
                    continue

                # Build solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Education", "Occupation"],
                        "rows": []
                    }
                }
                for i in range(3):
                    house = str(i + 1)
                    name = name_perm[i]
                    education = edu_perm[i]
                    occupation = occ_perm[i]
                    solution['solution']['rows'].append([house, name, education, occupation])
                return solution

    return {"solution": {"header": [], "rows": []}}

# Generate and print the JSON solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))