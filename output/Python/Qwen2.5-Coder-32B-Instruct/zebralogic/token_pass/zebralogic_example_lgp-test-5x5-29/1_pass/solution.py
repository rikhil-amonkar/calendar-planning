import itertools
import json

def solve_puzzle():
    # Define possible values for each attribute
    names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']

    # Create a list of all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names))
    all_permutations.extend(list(itertools.permutations(nationalities)))
    all_permutations.extend(list(itertools.permutations(vacations)))
    all_permutations.extend(list(itertools.permutations(educations)))
    all_permutations.extend(list(itertools.permutations(occupations)))

    # Check all combinations of permutations
    for names_perm in all_permutations[:len(names)]:
        for nationalities_perm in all_permutations[len(names):2*len(names)]:
            for vacations_perm in all_permutations[2*len(names):3*len(names)]:
                for educations_perm in all_permutations[3*len(names):4*len(names)]:
                    for occupations_perm in all_permutations[4*len(names):]:
                        if satisfies_constraints(names_perm, nationalities_perm, vacations_perm, educations_perm, occupations_perm):
                            # Format the solution as JSON
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                                    "rows": [
                                        [str(i+1), names_perm[i], nationalities_perm[i], vacations_perm[i], educations_perm[i], occupations_perm[i]]
                                        for i in range(5)
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

def satisfies_constraints(names, nationalities, vacations, educations, occupations):
    # Implement each constraint as a condition
    if occupations[vacations.index('cruise')] != 'lawyer':
        return False
    if names[vacations.index('beach') + 1] != 'Arnold':
        return False
    if educations.index('doctorate') > names.index('Bob'):
        return False
    if educations[vacations.index('cruise')] != 'associate':
        return False
    if names[0] == 'Peter':
        return False
    if occupations[names.index('Peter')] != 'artist':
        return False
    if educations[vacations.index('camping')] != 'master':
        return False
    if nationalities.index('dane') < occupations.index('doctor'):
        return False
    if educations.index('associate') + 1 != occupations.index('engineer'):
        return False
    if nationalities[vacations.index('camping')] != 'brit':
        return False
    if abs(nationalities.index('norwegian') - educations.index('bachelor')) != 1:
        return False
    if occupations[names.index('Eric')] != 'artist':
        return False
    if names.index('Alice') != nationalities.index('german'):
        return False
    if vacations.index('beach') >= vacations.index('city'):
        return False
    if occupations[vacations.index('mountain')] != names[4]:
        return False
    if vacations.index('cruise') <= vacations.index('beach'):
        return False
    if educations[2] != 'bachelor':
        return False
    if names[3] == 'Bob':
        return False
    return True

# Solve the puzzle and print the result
print(solve_puzzle())