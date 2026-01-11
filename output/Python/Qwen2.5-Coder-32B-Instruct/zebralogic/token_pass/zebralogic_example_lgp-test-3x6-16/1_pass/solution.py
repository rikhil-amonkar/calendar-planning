import itertools
import json

# Define the attributes
names = ['Eric', 'Peter', 'Arnold']
drinks = ['tea', 'water', 'milk']
nationalities = ['dane', 'brit', 'swede']
educations = ['high school', 'associate', 'bachelor']
house_styles = ['victorian', 'colonial', 'ranch']
smoothies = ['cherry', 'watermelon', 'desert']

# Function to check if a given assignment satisfies all the clues
def is_valid(assignment):
    # Unpack the assignment
    (name1, drink1, nationality1, education1, house_style1, smoothie1), \
    (name2, drink2, nationality2, education2, house_style2, smoothie2), \
    (name3, drink3, nationality3, education3, house_style3, smoothie3) = assignment
    
    # Check each clue
    if abs(names.index('Eric') - drinks.index('tea')) != 1: return False  # Clue 1
    if drinks.index('milk') != house_styles.index('ranch'): return False  # Clue 2
    if educations.index('bachelor') != 1: return False  # Clue 3
    if nationalities.index('dane') != educations.index('high school'): return False  # Clue 4
    if smoothies.index('desert') != nationalities.index('swede'): return False  # Clue 5
    if house_styles.index('victorian') == 0: return False  # Clue 6
    if smoothies.index('cherry') != house_styles.index('colonial'): return False  # Clue 7
    if house_styles.index('victorian') > names.index('Arnold'): return False  # Clue 8
    if drinks.index('milk') != educations.index('high school'): return False  # Clue 9
    
    return True

# Generate all permutations of the attributes
all_permutations = itertools.permutations(names)
for name_perm in all_permutations:
    for drink_perm in itertools.permutations(drinks):
        for nationality_perm in itertools.permutations(nationalities):
            for education_perm in itertools.permutations(educations):
                for house_style_perm in itertools.permutations(house_styles):
                    for smoothie_perm in itertools.permutations(smoothies):
                        assignment = list(zip(name_perm, drink_perm, nationality_perm, 
                                             education_perm, house_style_perm, smoothie_perm))
                        if is_valid(assignment):
                            # Format the solution as JSON
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                                    "rows": [
                                        ["1", name_perm[0], drink_perm[0], nationality_perm[0], education_perm[0], house_style_perm[0], smoothie_perm[0]],
                                        ["2", name_perm[1], drink_perm[1], nationality_perm[1], education_perm[1], house_style_perm[1], smoothie_perm[1]],
                                        ["3", name_perm[2], drink_perm[2], nationality_perm[2], education_perm[2], house_style_perm[2], smoothie_perm[2]]
                                    ]
                                }
                            }
                            print(json.dumps(solution, indent=2))
                            exit()