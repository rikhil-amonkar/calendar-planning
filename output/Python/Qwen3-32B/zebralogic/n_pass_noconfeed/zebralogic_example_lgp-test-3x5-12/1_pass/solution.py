import itertools
import json

names = ['Eric', 'Peter', 'Arnold']
cigars = ['blue master', 'prince', 'pall mall']
hobbies = ['photography', 'gardening', 'cooking']
education = ['high school', 'associate', 'bachelor']
drinks = ['tea', 'milk', 'water']

for name_p in itertools.permutations(names):
    for cigar_p in itertools.permutations(cigars):
        # Constraint 1: Pall Mall is Peter
        pm_valid = True
        for i in range(3):
            if cigar_p[i] == 'pall mall' and name_p[i] != 'Peter':
                pm_valid = False
                break
        if not pm_valid:
            continue

        for hobby_p in itertools.permutations(hobbies):
            for edu_p in itertools.permutations(education):
                for drink_p in itertools.permutations(drinks):
                    # Constraint 3: Eric drinks tea
                    if any(name_p[i] == 'Eric' and drink_p[i] != 'tea' for i in range(3)):
                        continue

                    # Constraint 2 and 6: Milk drinker
                    milk_idx = None
                    for i in range(3):
                        if drink_p[i] == 'milk':
                            milk_idx = i
                            break
                    if milk_idx is None or milk_idx == 2:
                        continue
                    if edu_p[milk_idx] != 'associate' or edu_p[milk_idx + 1] != 'high school':
                        continue

                    # Constraint 4: Arnold and Prince adjacent
                    arnold_idx = None
                    prince_idx = None
                    for i in range(3):
                        if name_p[i] == 'Arnold':
                            arnold_idx = i
                        if cigar_p[i] == 'prince':
                            prince_idx = i
                    if arnold_idx is None or prince_idx is None:
                        continue
                    if abs(arnold_idx - prince_idx) != 1:
                        continue

                    # Constraint 5: Gardening left of Prince
                    garden_idx = None
                    for i in range(3):
                        if hobby_p[i] == 'gardening':
                            garden_idx = i
                            break
                    if garden_idx is None or garden_idx >= prince_idx:
                        continue

                    # Constraint 7: Bachelor left of photography
                    bachelor_idx = None
                    for i in range(3):
                        if edu_p[i] == 'bachelor':
                            bachelor_idx = i
                            break
                    if bachelor_idx is None or bachelor_idx == 2:
                        continue
                    if hobby_p[bachelor_idx + 1] != 'photography':
                        continue

                    # Build solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                            "rows": []
                        }
                    }
                    for i in range(3):
                        house_num = str(i + 1)
                        solution["solution"]["rows"].append([
                            house_num,
                            name_p[i],
                            cigar_p[i],
                            hobby_p[i],
                            edu_p[i],
                            drink_p[i]
                        ])
                    print(json.dumps(solution))
                    exit()