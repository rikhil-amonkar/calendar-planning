import itertools
import json

def find_solution():
    names_list = ['Peter', 'Eric', 'Arnold']
    edu_list = ['bachelor', 'associate', 'high school']
    occ_list = ['teacher', 'doctor', 'engineer']
    
    for names in itertools.permutations(names_list):
        for educations in itertools.permutations(edu_list):
            for occupations in itertools.permutations(occ_list):
                peter_index = names.index('Peter')
                if educations[peter_index] != 'high school':
                    continue
                    
                doctor_index = occupations.index('doctor')
                if educations[doctor_index] != 'bachelor':
                    continue
                    
                if (occupations[0] == 'teacher' and educations[1] == 'associate') or (occupations[1] == 'teacher' and educations[2] == 'associate'):
                    pass
                else:
                    continue
                    
                associate_index = educations.index('associate')
                eric_index = names.index('Eric')
                if abs(associate_index - eric_index) != 1:
                    continue
                    
                return (names, educations, occupations)
                
    return None

sol = find_solution()
if sol is not None:
    names, educations, occupations = sol
    header = ["House", "Name", "Education", "Occupation"]
    rows = []
    for i in range(3):
        rows.append([str(i+1), names[i], educations[i], occupations[i]])
    solution_dict = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(solution_dict))
else:
    print('{"error": "No solution found"}')