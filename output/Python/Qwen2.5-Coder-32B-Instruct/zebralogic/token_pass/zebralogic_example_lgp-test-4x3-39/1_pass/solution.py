import itertools
import json

# Define the variables
names = ['Eric', 'Alice', 'Peter', 'Arnold']
hair_colors = ['blonde', 'black', 'red', 'brown']
favorite_sports = ['swimming', 'soccer', 'basketball', 'tennis']

# Define the constraints as functions
def constraint1(sports):
    return sports[1] != 'soccer'

def constraint2(names, hair_colors):
    return hair_colors[names.index('Eric')] == 'blonde'

def constraint3(hair_colors, favorite_sports):
    blonde_index = hair_colors.index('blonde')
    basketball_index = favorite_sports.index('basketball')
    return blonde_index > basketball_index

def constraint4(hair_colors, favorite_sports):
    return hair_colors[favorite_sports.index('tennis')] == 'black'

def constraint5(names, hair_colors):
    arnold_index = names.index('Arnold')
    red_hair_index = hair_colors.index('red')
    return arnold_index < red_hair_index

def constraint6(names, favorite_sports):
    return favorite_sports[names.index('Alice')] == 'swimming'

def constraint7(hair_colors):
    red_hair_index = hair_colors.index('red')
    black_hair_index = hair_colors.index('black')
    return red_hair_index + 1 == black_hair_index

# Generate all permutations
all_permutations = list(itertools.permutations(range(4)))

# Check each permutation against the constraints
for names_perm in all_permutations:
    for hair_colors_perm in all_permutations:
        for favorite_sports_perm in all_permutations:
            names_arranged = [names[i] for i in names_perm]
            hair_colors_arranged = [hair_colors[i] for i in hair_colors_perm]
            favorite_sports_arranged = [favorite_sports[i] for i in favorite_sports_perm]
            
            if (constraint1(favorite_sports_arranged) and
                constraint2(names_arranged, hair_colors_arranged) and
                constraint3(hair_colors_arranged, favorite_sports_arranged) and
                constraint4(hair_colors_arranged, favorite_sports_arranged) and
                constraint5(names_arranged, hair_colors_arranged) and
                constraint6(names_arranged, favorite_sports_arranged) and
                constraint7(hair_colors_arranged)):
                
                # Construct the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "FavoriteSport"],
                        "rows": []
                    }
                }
                
                for i in range(4):
                    solution["solution"]["rows"].append([
                        str(i + 1),
                        names_arranged[i],
                        hair_colors_arranged[i],
                        favorite_sports_arranged[i]
                    ])
                
                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                break