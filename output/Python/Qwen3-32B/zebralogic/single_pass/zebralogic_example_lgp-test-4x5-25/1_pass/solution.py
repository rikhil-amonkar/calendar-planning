import itertools
import json

def solve():
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    house_styles = ['craftsman', 'colonial', 'victorian', 'ranch']
    hair_colors = ['red', 'blonde', 'black', 'brown']
    children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    book_genres = ['mystery', 'fantasy', 'romance', 'science fiction']

    for name_perm in itertools.permutations(names):
        for style_perm in itertools.permutations(house_styles):
            # Clue 1: Craftsman is in house 3 (index 2)
            if style_perm[2] != 'craftsman':
                continue
            # Clue 8: Alice is in colonial
            alice_house = name_perm.index('Alice')
            if style_perm[alice_house] != 'colonial':
                continue

            for hair_perm in itertools.permutations(hair_colors):
                # Clue 3: Brown hair in house 4 (index 3)
                if hair_perm[3] != 'brown':
                    continue
                # Clue 9: Black hair in house 2 (index 1)
                if hair_perm[1] != 'black':
                    continue
                # Clue 7: Arnold has red hair
                arnold_house = name_perm.index('Arnold')
                if hair_perm[arnold_house] != 'red':
                    continue
                # Clue 12: Black hair is Eric
                eric_house = name_perm.index('Eric')
                if hair_perm[eric_house] != 'black':
                    continue

                for child_perm in itertools.permutations(children):
                    # Clue 4: Child Samantha in house 4
                    if child_perm[3] != 'Samantha':
                        continue
                    # Clue 6: Peter's child is Bella
                    peter_house = name_perm.index('Peter')
                    if child_perm[peter_house] != 'Bella':
                        continue
                    # Clue 11: Arnold's child is Meredith
                    if child_perm[arnold_house] != 'Meredith':
                        continue

                    for book_perm in itertools.permutations(book_genres):
                        # Clue 2: Alice loves romance
                        if book_perm[alice_house] != 'romance':
                            continue
                        # Clue 10: Peter's book is fantasy
                        if book_perm[peter_house] != 'fantasy':
                            continue
                        # Clue 13: Arnold's book is science fiction
                        if book_perm[arnold_house] != 'science fiction':
                            continue

                        # Clue 5: Ranch is to the right of red hair (Arnold's house)
                        ranch_pos = style_perm.index('ranch')
                        if ranch_pos <= arnold_house:
                            continue

                        # Build solution
                        solution_rows = []
                        for i in range(4):
                            house_num = str(i + 1)
                            name = name_perm[i]
                            style = style_perm[i]
                            hair = hair_perm[i]
                            child = child_perm[i]
                            book = book_perm[i]
                            solution_rows.append([house_num, name, style, hair, child, book])

                        solution = {
                            "solution": {
                                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                                "rows": solution_rows
                            }
                        }
                        print(json.dumps(solution))
                        return

solve()