import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    house_styles = ['craftsman', 'colonial', 'victorian', 'ranch']
    hair_colors = ['red', 'blonde', 'black', 'brown']
    children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    book_genres = ['mystery', 'fantasy', 'romance', 'science fiction']

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(house_styles):
            for hair_perm in itertools.permutations(hair_colors):
                for child_perm in itertools.permutations(children):
                    for genre_perm in itertools.permutations(book_genres):
                        # Apply constraints
                        if (style_perm[2] == 'craftsman' and
                            name_perm[house_styles.index('colonial')] == 'Alice' and
                            hair_perm[3] == 'brown' and
                            child_perm[3] == 'Samantha' and
                            style_perm.index('ranch') > hair_perm.index('red') and
                            child_perm[names.index('Peter')] == 'Bella' and
                            hair_perm[names.index('Arnold')] == 'red' and
                            hair_perm[1] == 'black' and
                            name_perm[hair_colors.index('black')] == 'Eric' and
                            genre_perm[names.index('Peter')] == 'fantasy' and
                            child_perm[names.index('Arnold')] == 'Meredith' and
                            genre_perm[names.index('Arnold')] == 'science fiction' and
                            genre_perm[name_perm.index('Alice')] == 'romance'):
                            
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                                    "rows": [
                                        [str(houses[0]), name_perm[0], style_perm[0], hair_perm[0], child_perm[0], genre_perm[0]],
                                        [str(houses[1]), name_perm[1], style_perm[1], hair_perm[1], child_perm[1], genre_perm[1]],
                                        [str(houses[2]), name_perm[2], style_perm[2], hair_perm[2], child_perm[2], genre_perm[2]],
                                        [str(houses[3]), name_perm[3], style_perm[3], hair_perm[3], child_perm[3], genre_perm[3]]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

print(solve_puzzle())