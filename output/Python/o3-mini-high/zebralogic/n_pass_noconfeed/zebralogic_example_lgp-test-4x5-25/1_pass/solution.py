import itertools
import json

def main():
    names = ["Arnold", "Peter", "Eric", "Alice"]
    house_styles = ["craftsman", "colonial", "victorian", "ranch"]
    hair_colors = ["red", "blonde", "black", "brown"]
    children = ["Bella", "Fred", "Meredith", "Samantha"]
    book_genres = ["mystery", "fantasy", "romance", "science fiction"]

    solution_found = None

    for name_perm in itertools.permutations(names):
        # Constraint: The person with black hair (house2) must be Eric.
        if name_perm[1] != "Eric":
            continue

        for style_perm in itertools.permutations(house_styles):
            # Constraint 1: The person in a Craftsman-style house is in the third house.
            if style_perm[2] != "craftsman":
                continue

            for hair_perm in itertools.permutations(hair_colors):
                # Constraint 3: The person who has brown hair is in the fourth house.
                # Constraint 9: The person who has black hair is in the second house.
                if hair_perm[1] != "black" or hair_perm[3] != "brown":
                    continue

                for child_perm in itertools.permutations(children):
                    # Constraint 4: The person whose child is named Samantha is in the fourth house.
                    if child_perm[3] != "Samantha":
                        continue

                    for book_perm in itertools.permutations(book_genres):
                        valid = True
                        for i in range(4):
                            # Constraint 2 and 8: Alice lives in a colonial-style house and loves romance books.
                            if name_perm[i] == "Alice":
                                if style_perm[i] != "colonial" or book_perm[i] != "romance":
                                    valid = False
                                    break
                            # Constraint 7, 11, and 13: Arnold has red hair, his child is Meredith, and he loves science fiction.
                            elif name_perm[i] == "Arnold":
                                if hair_perm[i] != "red" or child_perm[i] != "Meredith" or book_perm[i] != "science fiction":
                                    valid = False
                                    break
                            # Constraint 6 and 10: Peter’s child is Bella and he loves fantasy books.
                            elif name_perm[i] == "Peter":
                                if child_perm[i] != "Bella" or book_perm[i] != "fantasy":
                                    valid = False
                                    break
                            # For Eric, by elimination his child must be Fred and his favorite genre mystery.
                            elif name_perm[i] == "Eric":
                                if child_perm[i] != "Fred" or book_perm[i] != "mystery":
                                    valid = False
                                    break
                        if not valid:
                            continue

                        # Constraint 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
                        try:
                            idx_ranch = style_perm.index("ranch")
                            idx_red = hair_perm.index("red")
                            if idx_red >= idx_ranch:
                                continue
                        except ValueError:
                            continue

                        # All constraints are satisfied.
                        solution_found = {
                            "names": name_perm,
                            "styles": style_perm,
                            "hair": hair_perm,
                            "children": child_perm,
                            "books": book_perm
                        }
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
        rows = []
        for i in range(4):
            rows.append([
                str(i + 1),
                solution_found["names"][i],
                solution_found["styles"][i],
                solution_found["hair"][i],
                solution_found["children"][i],
                solution_found["books"][i]
            ])
        final_solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                "rows": rows
            }
        }
        print(json.dumps(final_solution))

if __name__ == "__main__":
    main()