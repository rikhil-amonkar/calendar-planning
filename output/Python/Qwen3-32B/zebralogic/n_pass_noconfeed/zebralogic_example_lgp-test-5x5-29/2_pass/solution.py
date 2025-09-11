import itertools
import json
import sys  # Import sys module for sys.exit()

# Define the domains
names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
education_levels = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']

# Generate all possible permutations for each category
name_perms = itertools.permutations(names)
nat_perms = itertools.permutations(nationalities)
vac_perms = itertools.permutations(vacations)
edu_perms = itertools.permutations(education_levels)
occ_perms = itertools.permutations(occupations)

for names_p in name_perms:
    for nats_p in nat_perms:
        # Check if Alice is German, Peter is Swede, Eric is Brit
        if nats_p[names_p.index('Alice')] != 'german':
            continue
        if nats_p[names_p.index('Peter')] != 'swede':
            continue
        if nats_p[names_p.index('Eric')] != 'brit':
            continue
        for vacs_p in vac_perms:
            # Check if camping is in Eric's position
            eric_index = names_p.index('Eric')
            if vacs_p[eric_index] != 'camping':
                continue
            for edus_p in edu_perms:
                # Check if Eric's education is master
                if edus_p[eric_index] != 'master':
                    continue
                # Check if house 3's education is bachelor
                if edus_p[2] != 'bachelor':  # house 3 is index 2 (0-based)
                    continue
                for occs_p in occ_perms:
                    # Check if Peter's occupation is artist
                    peter_index = names_p.index('Peter')
                    if occs_p[peter_index] != 'artist':
                        continue
                    # Check if cruise lover is lawyer
                    cruise_index = vacs_p.index('cruise')
                    if occs_p[cruise_index] != 'lawyer':
                        continue
                    # Check if associate's degree is the cruise lover
                    if edus_p[cruise_index] != 'associate':
                        continue
                    # Check if mountain is in house 5 (index 4)
                    if vacs_p[4] != 'mountain':
                        continue
                    # Create a list of houses, each with their attributes
                    houses = []
                    for i in range(5):
                        house = {
                            'name': names_p[i],
                            'nationality': nats_p[i],
                            'vacation': vacs_p[i],
                            'education': edus_p[i],
                            'occupation': occs_p[i]
                        }
                        houses.append(house)
                    # Now check all other constraints
                    # Clue 2: beach is directly left of Arnold
                    beach_index = vacs_p.index('beach')
                    if beach_index + 1 >= 5 or houses[beach_index + 1]['name'] != 'Arnold':
                        continue
                    # Clue 3: doctorate is left of Bob
                    bob_index = names_p.index('Bob')
                    doctorate_index = edus_p.index('doctorate')
                    if doctorate_index >= bob_index:
                        continue
                    # Clue 9: associate is directly left of engineer
                    associate_index = edus_p.index('associate')
                    if associate_index + 1 >= 5 or occs_p[associate_index + 1] != 'engineer':
                        continue
                    # Clue 5: Peter not in first house
                    if peter_index == 0:
                        continue
                    # Clue 13: Bob not in fourth house (index 3)
                    if bob_index == 3:
                        continue
                    # Clue 8: Dane is right of doctor (occupation)
                    doctor_occ_index = occs_p.index('doctor')
                    dane_index = nats_p.index('dane')
                    if dane_index <= doctor_occ_index:
                        continue
                    # Clue 11: Norwegian and bachelor (house 3, index 2) are next to each other
                    norwegian_index = nats_p.index('norwegian')
                    if abs(norwegian_index - 2) != 1:
                        continue
                    # Clue 16: beach is left of city
                    beach_index = vacs_p.index('beach')
                    city_index = vacs_p.index('city')
                    if beach_index >= city_index:
                        continue
                    # Clue 18: cruise is right of beach
                    cruise_index = vacs_p.index('cruise')
                    if cruise_index <= beach_index:
                        continue
                    # All constraints are satisfied
                    # Now, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                            "rows": []
                        }
                    }
                    for i in range(5):
                        house_num = str(i + 1)
                        row = [
                            house_num,
                            houses[i]['name'],
                            houses[i]['nationality'],
                            houses[i]['vacation'],
                            houses[i]['education'],
                            houses[i]['occupation']
                        ]
                        solution['solution']['rows'].append(row)
                    print(json.dumps(solution))
                    sys.exit()  # Use sys.exit() instead of exit()