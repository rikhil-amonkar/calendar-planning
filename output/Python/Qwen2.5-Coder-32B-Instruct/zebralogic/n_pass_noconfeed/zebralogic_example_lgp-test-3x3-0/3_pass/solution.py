import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ['Peter', 'Eric', 'Arnold']
    educations = ['bachelor', 'associate', 'high school']
    occupations = ['teacher', 'doctor', 'engineer']
    
    # Iterate through all possible combinations
    for name_perm in itertools.permutations(names):
        for education_perm in itertools.permutations(educations):
            for occupation_perm in itertools.permutations(occupations):
                # Unpack the permutations
                name1, name2, name3 = name_perm
                edu1, edu2, edu3 = education_perm
                occ1, occ2, occ3 = occupation_perm
                
                # Check the clues
                if (occ1 == 'teacher' and edu2 == 'associate' and
                    abs(name_perm.index('Eric') - education_perm.index('associate')) == 1 and
                    name1 == 'Peter' and edu1 == 'high school' and
                    occ2 == 'doctor' and edu3 == 'bachelor'):
                    
                    # Construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Education", "Occupation"],
                            "rows": [
                                ["1", name1, edu1, occ1],
                                ["2", name2, edu2, occ2],
                                ["3", name3, edu3, occ3]
                            ]
                        }
                    }
                    
                    # Output the solution as JSON
                    print(json.dumps(solution, indent=2))
                    return

# Run the solver
solve_puzzle()