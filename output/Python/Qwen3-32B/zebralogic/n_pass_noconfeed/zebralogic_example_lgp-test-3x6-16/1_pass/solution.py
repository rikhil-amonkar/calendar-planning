import itertools
import json

categories = {
    'names': ['Eric', 'Peter', 'Arnold'],
    'drinks': ['tea', 'water', 'milk'],
    'nationalities': ['dane', 'brit', 'swede'],
    'educations': ['high school', 'associate', 'bachelor'],
    'housestyles': ['victorian', 'colonial', 'ranch'],
    'smoothies': ['cherry', 'watermelon', 'desert'],
}

# Generate permutations with pre-filters where possible
all_name_perms = list(itertools.permutations(categories['names']))
all_drink_perms = list(itertools.permutations(categories['drinks']))
all_nat_perms = list(itertools.permutations(categories['nationalities']))
all_edu_perms = [p for p in itertools.permutations(categories['educations']) if p[1] == 'bachelor']
all_housestyle_perms = [p for p in itertools.permutations(categories['housestyles']) if p[0] != 'victorian']
all_smoothie_perms = list(itertools.permutations(categories['smoothies']))

for name_p, drink_p, nat_p, edu_p, house_p, smoothie_p in itertools.product(
        all_name_perms, all_drink_perms, all_nat_perms, all_edu_perms, 
        all_housestyle_perms, all_smoothie_perms):

    # Check clue 9: ranch house has high school education
    ranch_pos = house_p.index('ranch')
    if edu_p[ranch_pos] != 'high school':
        continue

    # Check clue 4: high school is Dane
    hs_pos = edu_p.index('high school')
    if nat_p[hs_pos] != 'dane':
        continue

    # Check clue 5: desert smoothie lover is swede
    desert_pos = smoothie_p.index('desert')
    if nat_p[desert_pos] != 'swede':
        continue

    # Check clue 7: cherry smoothie is in colonial house
    try:
        cherry_pos = smoothie_p.index('cherry')
    except ValueError:
        continue
    if house_p[cherry_pos] != 'colonial':
        continue

    # Check clue 8: Arnold is to the right of Victorian house
    vic_pos = house_p.index('victorian')
    arnold_pos = name_p.index('Arnold')
    if arnold_pos <= vic_pos:
        continue

    # Check clue 1: one house between Eric and tea
    eric_pos = name_p.index('Eric')
    tea_pos = drink_p.index('tea')
    if abs(eric_pos - tea_pos) != 2:
        continue

    # Check clue 2: milk drinker is in ranch
    milk_pos = drink_p.index('milk')
    if house_p[milk_pos] != 'ranch':
        continue

    # If all checks passed, build the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
            "rows": []
        }
    }
    for i in range(3):
        house_num = str(i + 1)
        row = [
            house_num,
            name_p[i],
            drink_p[i],
            nat_p[i],
            edu_p[i],
            house_p[i],
            smoothie_p[i]
        ]
        solution['solution']['rows'].append(row)

    print(json.dumps(solution, indent=2))
    exit()

print("No solution found.")