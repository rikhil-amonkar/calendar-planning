import itertools
import json

def solve_puzzle():
    # Define all possible values for each attribute
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    flowers = ['daffodils', 'carnations', 'roses', 'lilies']
    heights = ['very short', 'short', 'tall', 'average']
    mothers = ['Janelle', 'Kailyn', 'Holly', 'Aniya']
    occupations = ['engineer', 'doctor', 'teacher', 'artist']
    sports = ['swimming', 'basketball', 'tennis', 'soccer']

    # Generate all possible permutations of each attribute
    all_permutations = list(itertools.permutations(range(4)))

    # Check all combinations of permutations
    for name_perm in all_permutations:
        for flower_perm in all_permutations:
            for height_perm in all_permutations:
                for mother_perm in all_permutations:
                    for occupation_perm in all_permutations:
                        for sport_perm in all_permutations:
                            # Assign values based on permutations
                            house_data = {
                                1: {'Name': names[name_perm[0]], 'Flower': flowers[flower_perm[0]],
                                    'Height': heights[height_perm[0]], 'Mother': mothers[mother_perm[0]],
                                    'Occupation': occupations[occupation_perm[0]], 'FavoriteSport': sports[sport_perm[0]]},
                                2: {'Name': names[name_perm[1]], 'Flower': flowers[flower_perm[1]],
                                    'Height': heights[height_perm[1]], 'Mother': mothers[mother_perm[1]],
                                    'Occupation': occupations[occupation_perm[1]], 'FavoriteSport': sports[sport_perm[1]]},
                                3: {'Name': names[name_perm[2]], 'Flower': flowers[flower_perm[2]],
                                    'Height': heights[height_perm[2]], 'Mother': mothers[mother_perm[2]],
                                    'Occupation': occupations[occupation_perm[2]], 'FavoriteSport': sports[sport_perm[2]]},
                                4: {'Name': names[name_perm[3]], 'Flower': flowers[flower_perm[3]],
                                    'Height': heights[height_perm[3]], 'Mother': mothers[mother_perm[3]],
                                    'Occupation': occupations[occupation_perm[3]], 'FavoriteSport': sports[sport_perm[3]]}
                            }

                            # Check all clues
                            if (house_data[house_data['Eric']['Flower'] == 'roses']['FavoriteSport'] == 'swimming' and
                                house_data[1]['Occupation'] == 'teacher' and
                                house_data['Arnold']['Height'] == 'tall' and
                                flower_perm.index(flowers.index('daffodils')) > name_perm.index(names.index('engineer')) and
                                house_data['short']['FavoriteSport'] == 'soccer' and
                                house_data['Janelle']['Flower'] == 'carnations' and
                                house_data['average']['FavoriteSport'] == 'basketball' and
                                name_perm.index(names.index('Arnold')) != 2 and
                                mother_perm.index(mothers.index('Holly')) > height_perm.index(heights.index('average')) and
                                house_data['Peter']['Occupation'] == 'doctor' and
                                house_data['Aniya']['Name'] == 'Alice' and
                                house_data['Arnold']['Flower'] == 'lilies'):
                                
                                # Format the solution as JSON
                                solution_rows = []
                                for house_number in range(1, 5):
                                    row = [str(house_number)] + [
                                        house_data[house_number][key] for key in 
                                        ["Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"]
                                    ]
                                    solution_rows.append(row)
                                
                                solution_dict = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                                        "rows": solution_rows
                                    }
                                }
                                return json.dumps(solution_dict, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())