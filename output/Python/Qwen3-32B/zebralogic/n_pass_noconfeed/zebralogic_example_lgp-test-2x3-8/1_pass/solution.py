import itertools
import json

def solve_puzzle():
    names = ['Arnold', 'Eric']
    mothers = ['Aniya', 'Holly']
    birthdays = ['april', 'sept']
    
    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for birthday_perm in itertools.permutations(birthdays):
                # Check clue 2: April is in the first house
                if birthday_perm[0] != 'april':
                    continue
                
                # Check clue 1: Eric is left of Holly's mother
                eric_index = name_perm.index('Eric')
                holly_index = mother_perm.index('Holly')
                if eric_index < holly_index:
                    solution_rows = []
                    for i in range(2):
                        house_num = i + 1
                        name = name_perm[i]
                        birthday = birthday_perm[i]
                        mother = mother_perm[i]
                        solution_rows.append([
                            str(house_num), name, birthday, mother
                        ])
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Birthday", "Mother"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(solution))
                    return

solve_puzzle()