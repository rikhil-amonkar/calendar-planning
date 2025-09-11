import itertools
import json

def main():
    # Define the categories
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    house_styles = ['craftsman', 'colonial', 'victorian', 'ranch']
    hair_colors = ['red', 'blonde', 'black', 'brown']
    children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    book_genres = ['mystery', 'fantasy', 'romance', 'science fiction']

    # Generate filtered permutations for each category
    # House styles: third house (index 2) is 'craftsman'
    filtered_hs_perms = [p for p in itertools.permutations(house_styles) if p[2] == 'craftsman']

    # Hair colors: house 2 (index 1) is 'black', house 4 (index 3) is 'brown'
    filtered_hair_perms = [p for p in itertools.permutations(hair_colors) if p[1] == 'black' and p[3] == 'brown']

    # Children: house 4 (index 3) is 'Samantha'
    filtered_children_perms = [p for p in itertools.permutations(children) if p[3] == 'Samantha']

    # Book genres: all permutations
    book_perms = list(itertools.permutations(book_genres))

    # Names: all permutations
    names_perms = list(itertools.permutations(names))

    # Now iterate through all possible combinations
    for name_perm in names_perms:
        # Check clue 12: the person with black hair (house 2) is Eric → name_perm[1] must be Eric
        if name_perm[1] != 'Eric':
            continue

        for hs_perm in filtered_hs_perms:
            for hair_perm in filtered_hair_perms:
                for children_perm in filtered_children_perms:
                    for book_perm in book_perms:
                        valid = True

                        # Check clue 7: Arnold has red hair
                        arnold_idx = None
                        for i in range(4):
                            if name_perm[i] == 'Arnold':
                                arnold_idx = i
                                if hair_perm[i] != 'red':
                                    valid = False
                                    break
                        if not valid:
                            continue

                        # Check clue 13: Arnold's book is science fiction
                        for i in range(4):
                            if name_perm[i] == 'Arnold' and book_perm[i] != 'science fiction':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Check clue 11: Arnold's child is Meredith
                        for i in range(4):
                            if name_perm[i] == 'Arnold' and children_perm[i] != 'Meredith':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Check clue 6: Peter's child is Bella
                        for i in range(4):
                            if name_perm[i] == 'Peter' and children_perm[i] != 'Bella':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Check clue 10: Peter's book is fantasy
                        for i in range(4):
                            if name_perm[i] == 'Peter' and book_perm[i] != 'fantasy':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Check clue 2: Alice's book is romance
                        for i in range(4):
                            if name_perm[i] == 'Alice' and book_perm[i] != 'romance':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Check clue 8: Alice's house style is colonial
                        for i in range(4):
                            if name_perm[i] == 'Alice' and hs_perm[i] != 'colonial':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Check clue 5: ranch is to the right of red hair
                        red_idx = hair_perm.index('red')
                        ranch_idx = hs_perm.index('ranch')
                        if ranch_idx <= red_idx:
                            valid = False

                        if valid:
                            # Build the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                                    "rows": []
                                }
                            }
                            for i in range(4):
                                house_num = str(i + 1)
                                name = name_perm[i]
                                house_style = hs_perm[i]
                                hair_color = hair_perm[i]
                                child = children_perm[i]
                                book_genre = book_perm[i]
                                solution["solution"]["rows"].append([
                                    house_num, name, house_style, hair_color, child, book_genre
                                ])
                            print(json.dumps(solution, indent=2))
                            return  # exit after finding first solution

if __name__ == "__main__":
    main()