#!/usr/bin/env python3
import json
import itertools

def solve():
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["craftsman", "colonial", "victorian", "ranch"]
    hairs = ["red", "blonde", "black", "brown"]
    children = ["Bella", "Fred", "Meredith", "Samantha"]
    genres = ["mystery", "fantasy", "romance", "science fiction"]

    solution = None

    # Iterate over all possible assignments for each attribute category.
    # Each permutation list represents houses 1 to 4 (index 0 to 3).
    for names_perm in itertools.permutations(names):
        # Clue 9 & 12: The person in the second house must have black hair,
        # and the person with black hair is Eric.
        # Thus, the second house (index 1) must be Eric.
        if names_perm[1] != "Eric":
            continue
        index_arnold = names_perm.index("Arnold")
        index_peter = names_perm.index("Peter")
        index_alice = names_perm.index("Alice")

        for styles_perm in itertools.permutations(styles):
            # Clue 1: The person in a Craftsman-style house is in the third house.
            if styles_perm[2] != "craftsman":
                continue
            # Clue 8: Alice is the person living in a colonial-style house.
            if styles_perm[index_alice] != "colonial":
                continue
                
            for hair_perm in itertools.permutations(hairs):
                # Clue 3: The person who has brown hair is in the fourth house.
                if hair_perm[3] != "brown":
                    continue
                # Clue 9: The person in the second house has black hair.
                if hair_perm[1] != "black":
                    continue
                # Clue 7: Arnold is the person who has red hair.
                if hair_perm[index_arnold] != "red":
                    continue

                for child_perm in itertools.permutations(children):
                    # Clue 4: The person whose child is named Samantha is in the fourth house.
                    if child_perm[3] != "Samantha":
                        continue
                    # Clue 6: Peter's child is Bella.
                    if child_perm[index_peter] != "Bella":
                        continue
                    # Clue 11: Arnold's child is Meredith.
                    if child_perm[index_arnold] != "Meredith":
                        continue

                    for genres_perm in itertools.permutations(genres):
                        # Clue 2: Alice is the person who loves romance books.
                        if genres_perm[index_alice] != "romance":
                            continue
                        # Clue 10: The person who loves fantasy books is Peter.
                        if genres_perm[index_peter] != "fantasy":
                            continue
                        # Clue 13: The person who loves science fiction books is Arnold.
                        if genres_perm[index_arnold] != "science fiction":
                            continue
                            
                        # Clue 5: The person in a ranch-style home is somewhere
                        # to the right of the person who has red hair (Arnold).
                        try:
                            index_ranch = styles_perm.index("ranch")
                        except ValueError:
                            continue
                        if not (index_ranch > index_arnold):
                            continue
                            
                        # All constraints satisfied; build the solution.
                        solution = []
                        for i in range(4):
                            house_number = str(i + 1)
                            row = [
                                house_number,
                                names_perm[i],
                                styles_perm[i],
                                hair_perm[i],
                                child_perm[i],
                                genres_perm[i]
                            ]
                            solution.append(row)
                        break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "Style", "Hair", "Child", "Favorite Book Genre"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    solve()