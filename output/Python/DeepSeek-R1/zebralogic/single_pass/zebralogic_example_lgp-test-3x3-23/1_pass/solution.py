import itertools
import json

def main():
    names = ['Peter', 'Arnold', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    hobbies = ['cooking', 'photography', 'gardening']
    
    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            for hobby_perm in itertools.permutations(hobbies):
                # Constraint 1: Doctor and Eric are adjacent
                doctor_index = None
                eric_index = None
                for i in range(3):
                    if occ_perm[i] == 'doctor':
                        doctor_index = i
                    if name_perm[i] == 'Eric':
                        eric_index = i
                if doctor_index is None or eric_index is None:
                    continue
                if abs(doctor_index - eric_index) != 1:
                    continue
                
                # Constraint 2: Cooking left of teacher (directly adjacent)
                cooking_index = None
                teacher_index = None
                for i in range(3):
                    if hobby_perm[i] == 'cooking':
                        cooking_index = i
                    if occ_perm[i] == 'teacher':
                        teacher_index = i
                if cooking_index is None or teacher_index is None:
                    continue
                if teacher_index != cooking_index + 1:
                    continue
                
                # Constraint 3: Doctor right of gardening
                gardening_index = None
                for i in range(3):
                    if hobby_perm[i] == 'gardening':
                        gardening_index = i
                if gardening_index is None:
                    continue
                if doctor_index <= gardening_index:
                    continue
                
                # Constraint 4: Photography enthusiast is the teacher
                constraint4_ok = True
                for i in range(3):
                    if hobby_perm[i] == 'photography':
                        if occ_perm[i] != 'teacher':
                            constraint4_ok = False
                            break
                if not constraint4_ok:
                    continue
                
                # Constraint 5: Engineer is Peter
                constraint5_ok = True
                for i in range(3):
                    if occ_perm[i] == 'engineer':
                        if name_perm[i] != 'Peter':
                            constraint5_ok = False
                            break
                if not constraint5_ok:
                    continue
                
                # Format the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Hobby"],
                        "rows": [
                            ["1", name_perm[0], occ_perm[0], hobby_perm[0]],
                            ["2", name_perm[1], occ_perm[1], hobby_perm[1]],
                            ["3", name_perm[2], occ_perm[2], hobby_perm[2]]
                        ]
                    }
                }
                print(json.dumps(solution))
                return
    
    # If no solution found, output empty solution
    print(json.dumps({"solution": {"header": ["House", "Name", "Occupation", "Hobby"], "rows": []}}))

if __name__ == "__main__":
    main()