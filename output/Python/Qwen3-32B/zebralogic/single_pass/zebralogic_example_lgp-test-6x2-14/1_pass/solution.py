import itertools
import json

def solve_puzzle():
    names_list = ['Peter', None, 'Bob', None, 'Carol', 'Eric']  # indexes 0-5 for houses 1-6
    possible_name_options = [('Arnold', 'Alice'), ('Alice', 'Arnold')]
    fixed_cigars = [None, None, 'pall mall', None, 'blue master', None]
    cigar_options = ['blends', 'yellow monster', 'dunhill', 'prince']
    solution_found = None

    for name_perm in possible_name_options:
        current_names = names_list.copy()
        current_names[1] = name_perm[0]
        current_names[3] = name_perm[1]

        for cigar_perm in itertools.permutations(cigar_options):
            current_cigars = fixed_cigars.copy()
            current_cigars[0] = cigar_perm[0]  # house 1
            current_cigars[1] = cigar_perm[1]  # house 2
            current_cigars[3] = cigar_perm[2]  # house 4
            current_cigars[5] = cigar_perm[3]  # house 6

            # Determine Arnold's house (1-based)
            arnold_house = 2 if current_names[1] == 'Arnold' else 4

            # Check clue 1: Arnold left of blends
            blends_pos = current_cigars.index('blends')
            blends_house = blends_pos + 1
            if arnold_house >= blends_house:
                continue

            # Check clue 3: Arnold left of prince
            prince_pos = current_cigars.index('prince')
            prince_house = prince_pos + 1
            if arnold_house >= prince_house:
                continue

            # Check clue 4: yellow monster and blends have one house between
            yellow_monster_pos = current_cigars.index('yellow monster')
            yellow_house = yellow_monster_pos + 1
            if abs(yellow_house - blends_house) != 2:
                continue

            # All constraints satisfied
            solution_rows = []
            for i in range(6):
                house_num = str(i + 1)
                name = current_names[i]
                cigar = current_cigars[i]
                solution_rows.append([house_num, name, cigar])

            solution_found = {
                "solution": {
                    "header": ["House", "Name", "Cigar"],
                    "rows": solution_rows
                }
            }
            break  # exit the cigar_perm loop
        if solution_found:
            break  # exit the name_perm loop

    print(json.dumps(solution_found, indent=2))

solve_puzzle()