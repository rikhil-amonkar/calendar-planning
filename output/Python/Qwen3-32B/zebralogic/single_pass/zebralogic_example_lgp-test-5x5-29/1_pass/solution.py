import itertools
import json

names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
vacations = ['cruise', 'mountain', 'beach', 'camping', 'city']
educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']

for vac_tuple in itertools.permutations(['cruise', 'beach', 'camping', 'city']):
    vacation = list(vac_tuple) + ['mountain']
    if vacation[2] == 'cruise':
        continue
    try:
        beach_pos = vacation.index('beach')
        cruise_pos = vacation.index('cruise')
        city_pos = vacation.index('city')
    except ValueError:
        continue
    if beach_pos >= cruise_pos or beach_pos >= city_pos:
        continue
    camping_pos = vacation.index('camping')
    cr_pos = vacation.index('cruise')
    fixed_education = {
        2: 'bachelor',
        cr_pos: 'associate',
        camping_pos: 'master'
    }
    remaining_education_values = [e for e in educations if e not in fixed_education.values()]
    remaining_education_positions = [i for i in range(5) if i not in fixed_education.keys()]
    for edu_perm in itertools.permutations(remaining_education_values):
        education = [''] * 5
        for k, v in fixed_education.items():
            education[k] = v
        for i, pos in enumerate(remaining_education_positions):
            education[pos] = edu_perm[i]
        arnold_pos = beach_pos + 1
        eric_pos = camping_pos
        if arnold_pos >= 5:
            continue
        remaining_names = [n for n in names if n not in ['Eric', 'Arnold']]
        remaining_positions = [i for i in range(5) if i not in [eric_pos, arnold_pos]]
        for name_perm in itertools.permutations(remaining_names):
            name = [''] * 5
            name[eric_pos] = 'Eric'
            name[arnold_pos] = 'Arnold'
            for i, pos in enumerate(remaining_positions):
                name[pos] = name_perm[i]
            if name[0] == 'Peter':
                continue
            if name[3] == 'Bob':
                continue
            peter_pos = name.index('Peter')
            known_occupations = {
                cr_pos: 'lawyer',
                cr_pos + 1: 'engineer',
                peter_pos: 'artist'
            }
            if cr_pos + 1 >= 5:
                continue
            remaining_occupations = [o for o in occupations if o not in ['lawyer', 'engineer', 'artist']]
            remaining_occupation_positions = [i for i in range(5) if i not in known_occupations.keys()]
            for occ_perm in itertools.permutations(remaining_occupations):
                occupation = [''] * 5
                for k, v in known_occupations.items():
                    occupation[k] = v
                for i, pos in enumerate(remaining_occupation_positions):
                    occupation[pos] = occ_perm[i]
                doctor_pos = None
                for i, occ in enumerate(occupation):
                    if occ == 'doctor':
                        doctor_pos = i
                        break
                if doctor_pos is None:
                    continue
                alice_pos = name.index('Alice')
                known_nationalities = {
                    camping_pos: 'brit',
                    peter_pos: 'swede',
                    alice_pos: 'german'
                }
                remaining_nationalities = [n for n in nationalities if n not in ['brit', 'swede', 'german']]
                remaining_nationality_positions = [i for i in range(5) if i not in known_nationalities.keys()]
                for nat_perm in itertools.permutations(remaining_nationalities):
                    nationality = [''] * 5
                    for k, v in known_nationalities.items():
                        nationality[k] = v
                    for i, pos in enumerate(remaining_nationality_positions):
                        nationality[pos] = nat_perm[i]
                    dane_pos = None
                    for i, nat in enumerate(nationality):
                        if nat == 'dane':
                            dane_pos = i
                            break
                    if dane_pos is None or dane_pos <= doctor_pos:
                        continue
                    bachelor_pos = 2
                    norwegian_pos = nationality.index('norwegian')
                    if abs(norwegian_pos - bachelor_pos) != 1:
                        continue
                    solution_rows = []
                    for house in range(5):
                        house_num = str(house + 1)
                        solution_rows.append([
                            house_num,
                            name[house],
                            nationality[house],
                            vacation[house],
                            education[house],
                            occupation[house]
                        ])
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                            "rows": solution_rows
                        }
                    }
                    print(json.dumps(solution))
                    exit()