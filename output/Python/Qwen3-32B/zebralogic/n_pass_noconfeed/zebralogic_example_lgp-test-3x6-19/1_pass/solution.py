import itertools
import json

# Define the possible values for each category
names = ['Arnold', 'Eric', 'Peter']
cigars = ['pall mall', 'blue master', 'prince']
animals = ['horse', 'cat', 'bird']
children = ['Bella', 'Fred', 'Meredith']
bookgenres = ['science fiction', 'romance', 'mystery']
phonemodels = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']

solution_found = None

# Generate all possible permutations for each category and check constraints
for names_p in itertools.permutations(names):
    for cigars_p in itertools.permutations(cigars):
        for animals_p in itertools.permutations(animals):
            for children_p in itertools.permutations(children):
                for bookgenres_p in itertools.permutations(bookgenres):
                    for phonemodels_p in itertools.permutations(phonemodels):
                        # Constraint 3: Pall Mall in the second house
                        if cigars_p[1] != 'pall mall':
                            continue
                        # Constraint 10: science fiction in the third house
                        if bookgenres_p[2] != 'science fiction':
                            continue
                        # Constraint 11: mystery not in the second house
                        if bookgenres_p[1] == 'mystery':
                            continue
                        # Constraint 9: science fiction user has Samsung Galaxy S21
                        sci_fi_idx = bookgenres_p.index('science fiction')
                        if phonemodels_p[sci_fi_idx] != 'samsung galaxy s21':
                            continue
                        # Constraint 6: iPhone directly left of Samsung Galaxy S21
                        try:
                            iphone_idx = phonemodels_p.index('iphone 13')
                            samsung_idx = phonemodels_p.index('samsung galaxy s21')
                            if samsung_idx != iphone_idx + 1:
                                continue
                        except ValueError:
                            continue
                        # Constraint 7: Child Fred is directly left of Arnold
                        try:
                            fred_idx = children_p.index('Fred')
                            arnold_idx = names_p.index('Arnold')
                            if arnold_idx != fred_idx + 1:
                                continue
                        except ValueError:
                            continue
                        # Constraint 8: Peter is to the left of Eric
                        peter_idx = names_p.index('Peter')
                        eric_idx = names_p.index('Eric')
                        if peter_idx >= eric_idx:
                            continue
                        # Constraint 1: Mystery book lover's child is Fred
                        mystery_ok = True
                        for i in range(3):
                            if bookgenres_p[i] == 'mystery' and children_p[i] != 'Fred':
                                mystery_ok = False
                                break
                        if not mystery_ok:
                            continue
                        # Constraint 2: Eric is the cat lover
                        cat_ok = True
                        for i in range(3):
                            if animals_p[i] == 'cat' and names_p[i] != 'Eric':
                                cat_ok = False
                                break
                        if not cat_ok:
                            continue
                        # Constraint 4: Horse keeper's child is Meredith
                        horse_ok = True
                        for i in range(3):
                            if animals_p[i] == 'horse' and children_p[i] != 'Meredith':
                                horse_ok = False
                                break
                        if not horse_ok:
                            continue
                        # Constraint 5: Bella's parent smokes Prince
                        bella_ok = True
                        for i in range(3):
                            if children_p[i] == 'Bella' and cigars_p[i] != 'prince':
                                bella_ok = False
                                break
                        if not bella_ok:
                            continue
                        
                        # If all constraints are satisfied, build the solution
                        solution_found = {
                            "solution": {
                                "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                                "rows": []
                            }
                        }
                        for i in range(3):
                            house_num = str(i + 1)
                            solution_found["solution"]["rows"].append([
                                house_num, names_p[i], cigars_p[i], animals_p[i], children_p[i],
                                bookgenres_p[i], phonemodels_p[i]
                            ])
                        # Break all loops once a solution is found
                        break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

# Output the solution as JSON
print(json.dumps(solution_found, indent=2))