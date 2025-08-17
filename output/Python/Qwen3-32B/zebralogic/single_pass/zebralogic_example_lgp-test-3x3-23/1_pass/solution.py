import itertools
import json

def solve_puzzle():
    names = ['Peter', 'Arnold', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    hobbies = ['cooking', 'photography', 'gardening']

    for name_perm in itertools.permutations(names):
        for occ_perm in itertools.permutations(occupations):
            for hobby_perm in itertools.permutations(hobbies):
                # Clue 5: The person who is an engineer is Peter
                engineer_index = occ_perm.index('engineer')
                if name_perm[engineer_index] != 'Peter':
                    continue

                # Clue 4: The photography enthusiast is the person who is a teacher
                valid_clue4 = True
                for i in range(3):
                    if hobby_perm[i] == 'photography' and occ_perm[i] != 'teacher':
                        valid_clue4 = False
                        break
                if not valid_clue4:
                    continue

                # Clue 2: The person who loves cooking is directly left of the person who is a teacher
                found = False
                for i in range(2):
                    if hobby_perm[i] == 'cooking' and occ_perm[i+1] == 'teacher':
                        found = True
                        break
                if not found:
                    continue

                # Clue 1: The person who is a doctor and Eric are next to each other
                doctor_pos = occ_perm.index('doctor')
                eric_pos = name_perm.index('Eric')
                if abs(doctor_pos - eric_pos) != 1:
                    continue

                # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening
                gardening_pos = hobby_perm.index('gardening')
                doctor_pos = occ_perm.index('doctor')
                if doctor_pos <= gardening_pos:
                    continue

                # All clues satisfied, format solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Hobby"],
                        "rows": []
                    }
                }
                for i in range(3):
                    house_num = str(i + 1)
                    name = name_perm[i]
                    occ = occ_perm[i]
                    hobby = hobby_perm[i]
                    solution["solution"]["rows"].append([house_num, name, occ, hobby])
                print(json.dumps(solution))
                return

solve_puzzle()