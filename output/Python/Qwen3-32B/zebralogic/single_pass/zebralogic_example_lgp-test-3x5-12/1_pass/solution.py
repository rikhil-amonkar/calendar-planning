import itertools
import json

# Define the possible values for each category
names = ['Eric', 'Peter', 'Arnold']
cigars = ['blue master', 'prince', 'pall mall']
hobbies = ['photography', 'gardening', 'cooking']
education = ['high school', 'associate', 'bachelor']
drinks = ['tea', 'milk', 'water']

# Generate all possible permutations for each category
name_perms = list(itertools.permutations(names))
cigar_perms = list(itertools.permutations(cigars))
hobby_perms = list(itertools.permutations(hobbies))
education_perms = list(itertools.permutations(education))
drink_perms = list(itertools.permutations(drinks))

# Iterate through all possible combinations of permutations
for names_p in name_perms:
    for cigars_p in cigar_perms:
        for hobbies_p in hobby_perms:
            for education_p in education_perms:
                for drinks_p in drink_perms:
                    # Constraint 1: Pall Mall is Peter
                    pall_mall_idx = cigars_p.index('pall mall')
                    if names_p[pall_mall_idx] != 'Peter':
                        continue
                    # Constraint 6: Milk drinker has associate degree
                    milk_idx = drinks_p.index('milk')
                    if education_p[milk_idx] != 'associate':
                        continue
                    # Constraint 3: Eric drinks tea
                    eric_idx = names_p.index('Eric')
                    if drinks_p[eric_idx] != 'tea':
                        continue
                    # Constraint 2: Milk is directly left of high school
                    if milk_idx == 2 or education_p[milk_idx + 1] != 'high school':
                        continue
                    # Constraint 4: Arnold and Prince smoker are next to each other
                    arnold_idx = names_p.index('Arnold')
                    prince_idx = cigars_p.index('prince')
                    if abs(arnold_idx - prince_idx) != 1:
                        continue
                    # Constraint 5: Gardening is left of Prince
                    garden_idx = hobbies_p.index('gardening')
                    prince_idx_5 = cigars_p.index('prince')
                    if garden_idx >= prince_idx_5:
                        continue
                    # Constraint 7: Bachelor directly left of photography
                    bachelor_idx = education_p.index('bachelor')
                    if bachelor_idx == 2 or hobbies_p[bachelor_idx + 1] != 'photography':
                        continue
                    
                    # If all constraints passed, build the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                            "rows": []
                        }
                    }
                    for i in range(3):
                        house_num = str(i + 1)
                        name = names_p[i]
                        cigar = cigars_p[i]
                        hobby = hobbies_p[i]
                        ed = education_p[i]
                        drink = drinks_p[i]
                        solution["solution"]["rows"].append([
                            house_num, name, cigar, hobby, ed, drink
                        ])
                    
                    # Output the JSON
                    print(json.dumps(solution))
                    exit()