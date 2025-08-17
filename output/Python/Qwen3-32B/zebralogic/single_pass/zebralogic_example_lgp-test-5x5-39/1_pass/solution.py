import itertools
import json

# Define the categories
names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold']
birthdays = ['feb', 'sept', 'april', 'jan', 'mar']
mothers = ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya']
occupations_list = ['engineer', 'doctor', 'lawyer', 'artist', 'teacher']
hair_colors = ['red', 'blonde', 'black', 'gray', 'brown']

# Possible birthday permutations based on clues 1 and 2
possible_birthdays = [
    ['feb', 'april', 'sept', 'jan', 'mar'],
    ['feb', 'sept', 'april', 'jan', 'mar']
]

for birthday in possible_birthdays:
    # Find the index of 'sept' in the current birthday
    i_sept = birthday.index('sept')
    for names_perm in itertools.permutations(names):
        # Check if the person in house 4 (index 3) is Bob
        if names_perm[3] != 'Bob':
            continue
        # Determine indices of Peter, Alice, and Arnold
        i_p = names_perm.index('Peter')
        i_a = names_perm.index('Alice')
        i_arnold = names_perm.index('Arnold')
        # Check if Peter or Alice is in house 3 (index 2)
        if i_p == 2 or i_a == 2:
            continue
        # Generate occupations based on names_perm
        occupations = []
        for i in range(5):
            if names_perm[i] == 'Eric':
                occupations.append('doctor')
            elif names_perm[i] == 'Peter':
                occupations.append('lawyer')
            elif names_perm[i] == 'Alice':
                occupations.append('teacher')
            elif i == 3:
                occupations.append('artist')
            else:
                occupations.append('engineer')
        # Generate hair colors based on names_perm
        hair = [''] * 5
        for i in range(5):
            if names_perm[i] == 'Peter':
                hair[i] = 'black'
            elif names_perm[i] == 'Arnold':
                hair[i] = 'blonde'
            elif names_perm[i] == 'Alice':
                hair[i] = 'gray'
            elif i == 3:
                hair[i] = 'brown'
            else:
                pass  # To be filled later
        # Assign remaining hair color to 'red'
        for i in range(5):
            if hair[i] == '':
                hair[i] = 'red'
        # Generate possible mothers permutations
        fixed_mothers_indices = {i_p, i_a, 2}
        remaining_indices = [i for i in range(5) if i not in fixed_mothers_indices]
        # There should be exactly two remaining indices
        if len(remaining_indices) != 2:
            continue
        for perm_mothers in itertools.permutations(['Penny', 'Aniya']):
            mothers_perm = [''] * 5
            mothers_perm[2] = 'Janelle'
            mothers_perm[i_p] = 'Holly'
            mothers_perm[i_a] = 'Kailyn'
            mothers_perm[remaining_indices[0]] = perm_mothers[0]
            mothers_perm[remaining_indices[1]] = perm_mothers[1]
            # Check constraint 7: Penny is left of black hair (i_p)
            i_penny = mothers_perm.index('Penny')
            if not (i_penny < i_p):
                continue
            # Check constraint 16: i_sept < i_a
            if not (i_sept < i_a):
                continue
            # Check constraint 11: i_arnold > i_sept
            if not (i_arnold > i_sept):
                continue
            # All constraints satisfied, build the solution
            rows = []
            for house_num in range(5):
                house = str(house_num + 1)
                name = names_perm[house_num]
                bday = birthday[house_num]
                mother = mothers_perm[house_num]
                occ = occupations[house_num]
                hcolor = hair[house_num]
                rows.append([house, name, bday, mother, occ, hcolor])
            solution = {
                "solution": {
                    "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                    "rows": rows
                }
            }
            print(json.dumps(solution, indent=2))
            exit()