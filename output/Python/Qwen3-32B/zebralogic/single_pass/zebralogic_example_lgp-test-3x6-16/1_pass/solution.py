import itertools
import json

def solve_puzzle():
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['tea', 'water', 'milk']
    nationalities = ['dane', 'brit', 'swede']
    education_levels = ['high school', 'associate', 'bachelor']
    house_styles = ['victorian', 'colonial', 'ranch']
    smoothies = ['cherry', 'watermelon', 'desert']

    for names_perm in itertools.permutations(names):
        for drinks_perm in itertools.permutations(drinks):
            for nationalities_perm in itertools.permutations(nationalities):
                for education_perm in itertools.permutations(education_levels):
                    if education_perm[1] != 'bachelor':
                        continue
                    for housestyles_perm in itertools.permutations(house_styles):
                        if housestyles_perm[0] == 'victorian':
                            continue
                        for smoothies_perm in itertools.permutations(smoothies):
                            # Check clue 9: ranch → high school
                            valid = True
                            for i in range(3):
                                if housestyles_perm[i] == 'ranch' and education_perm[i] != 'high school':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Check clue 1: Eric and tea
                            eric_house = names_perm.index('Eric')
                            tea_house = drinks_perm.index('tea')
                            if abs(eric_house - tea_house) != 2:
                                continue
                            
                            # Check clue 2: milk → ranch
                            for i in range(3):
                                if drinks_perm[i] == 'milk' and housestyles_perm[i] != 'ranch':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Check clue 4: high school → dane
                            for i in range(3):
                                if education_perm[i] == 'high school' and nationalities_perm[i] != 'dane':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Check clue 5: desert → swede
                            for i in range(3):
                                if smoothies_perm[i] == 'desert' and nationalities_perm[i] != 'swede':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Check clue 7: cherry → colonial
                            for i in range(3):
                                if smoothies_perm[i] == 'cherry' and housestyles_perm[i] != 'colonial':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Check clue 8: Arnold to the right of Victorian
                            arnold_house = names_perm.index('Arnold')
                            victorian_house = housestyles_perm.index('victorian')
                            if arnold_house <= victorian_house:
                                continue
                            
                            # Build solution
                            rows = []
                            for i in range(3):
                                house_num = str(i + 1)
                                name = names_perm[i]
                                drink = drinks_perm[i]
                                nationality = nationalities_perm[i]
                                education = education_perm[i]
                                housestyle = housestyles_perm[i]
                                smoothie = smoothies_perm[i]
                                rows.append([house_num, name, drink, nationality, education, housestyle, smoothie])
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                                    "rows": rows
                                }
                            }
                            return solution
    return None

# Generate and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))