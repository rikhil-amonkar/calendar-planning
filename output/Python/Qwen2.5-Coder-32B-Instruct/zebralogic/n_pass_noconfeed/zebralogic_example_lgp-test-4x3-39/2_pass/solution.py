import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ['Eric', 'Alice', 'Peter', 'Arnold']
    hair_colors = ['blonde', 'black', 'red', 'brown']
    favorite_sports = ['swimming', 'soccer', 'basketball', 'tennis']

    # Generate all possible permutations for each category
    name_permutations = list(itertools.permutations(names))
    hair_color_permutations = list(itertools.permutations(hair_colors))
    sport_permutations = list(itertools.permutations(favorite_sports))

    # Iterate over all combinations of permutations
    for name_perm in name_permutations:
        for hair_color_perm in hair_color_permutations:
            for sport_perm in sport_permutations:
                # Apply constraints
                if (sport_perm[1] != 'soccer' and
                    name_perm.index('Eric') == hair_color_perm.index('blonde') and
                    hair_color_perm.index('blonde') > sport_perm.index('basketball') and
                    hair_color_perm.index('black') == sport_perm.index('tennis') and
                    name_perm.index('Arnold') < hair_color_perm.index('red') and
                    name_perm.index('Alice') == sport_perm.index('swimming') and
                    hair_color_perm.index('red') + 1 == hair_color_perm.index('black')):
                    
                    # Create the solution dictionary
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "FavoriteSport"],
                            "rows": []
                        }
                    }
                    
                    for i in range(4):
                        solution["solution"]["rows"].append([
                            str(houses[i]),
                            name_perm[i],
                            hair_color_perm[i],
                            sport_perm[i]
                        ])
                    
                    # Output the solution as JSON
                    print(json.dumps(solution, indent=2))
                    return

if __name__ == "__main__":
    solve_puzzle()