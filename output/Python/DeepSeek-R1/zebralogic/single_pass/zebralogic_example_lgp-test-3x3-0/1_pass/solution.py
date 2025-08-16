import itertools
import json

def main():
    names = ['Peter', 'Eric', 'Arnold']
    educations = ['bachelor', 'associate', 'high school']
    occupations = ['teacher', 'doctor', 'engineer']
    
    perms_names = list(itertools.permutations(names))
    perms_edus = list(itertools.permutations(educations))
    perms_occs = list(itertools.permutations(occupations))
    
    for p_name in perms_names:
        for p_edu in perms_edus:
            for p_occ in perms_occs:
                candidate = [
                    [p_name[0], p_edu[0], p_occ[0]],
                    [p_name[1], p_edu[1], p_occ[1]],
                    [p_name[2], p_edu[2], p_occ[2]]
                ]
                
                # Constraint 1: Teacher directly left of associate
                const1 = False
                for i in [0, 1]:
                    if candidate[i][2] == 'teacher' and candidate[i+1][1] == 'associate':
                        const1 = True
                        break
                if not const1:
                    continue
                
                # Constraint 2: Eric and associate adjacent
                idx_eric = None
                for i in range(3):
                    if candidate[i][0] == 'Eric':
                        idx_eric = i
                        break
                idx_associate = None
                for i in range(3):
                    if candidate[i][1] == 'associate':
                        idx_associate = i
                        break
                if idx_eric is None or idx_associate is None or abs(idx_eric - idx_associate) != 1:
                    continue
                
                # Constraint 3: Peter has high school diploma
                idx_peter = None
                for i in range(3):
                    if candidate[i][0] == 'Peter':
                        idx_peter = i
                        break
                if idx_peter is None or candidate[idx_peter][1] != 'high school':
                    continue
                
                # Constraint 4: Doctor has bachelor's degree
                idx_doctor = None
                for i in range(3):
                    if candidate[i][2] == 'doctor':
                        idx_doctor = i
                        break
                if idx_doctor is None or candidate[idx_doctor][1] != 'bachelor':
                    continue
                
                # Format solution
                solution_rows = [
                    ["1", candidate[0][0], candidate[0][1], candidate[0][2]],
                    ["2", candidate[1][0], candidate[1][1], candidate[1][2]],
                    ["3", candidate[2][0], candidate[2][1], candidate[2][2]]
                ]
                result = {
                    "solution": {
                        "header": ["House", "Name", "Education", "Occupation"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(result))
                return
                
    # If no solution found, output empty solution
    print(json.dumps({"solution": {"header": ["House", "Name", "Education", "Occupation"], "rows": []}}))

if __name__ == "__main__":
    main()