import itertools
import json

def solve_puzzle():
    names = ['Peter', 'Arnold', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    hobbies = ['cooking', 'photography', 'gardening']
    
    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            # Check clue5: engineer is Peter
            engineer_idx = occ_perm.index('engineer')
            if name_perm[engineer_idx] != 'Peter':
                continue
            
            teacher_idx = occ_perm.index('teacher')
            for hobby_perm in itertools.permutations(hobbies):
                # Check clue4: teacher's hobby is photography
                if hobby_perm[teacher_idx] != 'photography':
                    continue
                
                # Check clue2: cooking directly left of teacher
                if teacher_idx < 1 or hobby_perm[teacher_idx - 1] != 'cooking':
                    continue
                
                # Check clue3: doctor is to the right of gardening
                doctor_idx = occ_perm.index('doctor')
                gardening_idx = hobby_perm.index('gardening')
                if doctor_idx <= gardening_idx:
                    continue
                
                # Check clue1: doctor and Eric are adjacent
                eric_idx = name_perm.index('Eric')
                if abs(doctor_idx - eric_idx) != 1:
                    continue
                
                # Build solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Hobby"],
                        "rows": []
                    }
                }
                for i in range(3):
                    house_num = str(i + 1)
                    solution['solution']['rows'].append([
                        house_num, 
                        name_perm[i], 
                        occ_perm[i], 
                        hobby_perm[i]
                    ])
                
                print(json.dumps(solution))
                return

solve_puzzle()