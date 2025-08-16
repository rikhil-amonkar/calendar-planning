import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric", "Peter"]
    cigars = ["pall mall", "blue master", "prince"]
    animals = ["horse", "cat", "bird"]
    children = ["Bella", "Fred", "Meredith"]
    book_genres = ["science fiction", "romance", "mystery"]
    phone_models = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(cigars)) * \
                       list(itertools.permutations(animals)) * \
                       list(itertools.permutations(children)) * \
                       list(itertools.permutations(book_genres)) * \
                       list(itertools.permutations(phone_models))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(solution):
        (name_order, cigar_order, animal_order, children_order, book_genre_order, phone_model_order) = solution

        # Unpack the solution into house-specific data
        house1 = {"name": name_order[0], "cigar": cigar_order[0], "animal": animal_order[0], "children": children_order[0], "book_genre": book_genre_order[0], "phone_model": phone_model_order[0]}
        house2 = {"name": name_order[1], "cigar": cigar_order[1], "animal": animal_order[1], "children": children_order[1], "book_genre": book_genre_order[1], "phone_model": phone_model_order[1]}
        house3 = {"name": name_order[2], "cigar": cigar_order[2], "animal": animal_order[2], "children": children_order[2], "book_genre": book_genre_order[2], "phone_model": phone_model_order[2]}

        # Check each clue
        if house1["book_genre"] == "mystery" and house1["children"] != "Fred":
            return False
        if house2["book_genre"] == "mystery" and house2["children"] != "Fred":
            return False
        if house3["book_genre"] == "mystery" and house3["children"] != "Fred":
            return False
        if house1["animal"] == "cat" and house1["name"] != "Eric":
            return False
        if house2["animal"] == "cat" and house2["name"] != "Eric":
            return False
        if house3["animal"] == "cat" and house3["name"] != "Eric":
            return False
        if house2["cigar"] != "pall mall":
            return False
        if house1["animal"] == "horse" and house1["children"] != "Meredith":
            return False
        if house2["animal"] == "horse" and house2["children"] != "Meredith":
            return False
        if house3["animal"] == "horse" and house3["children"] != "Meredith":
            return False
        if house1["cigar"] == "prince" and house1["children"] != "Bella":
            return False
        if house2["cigar"] == "prince" and house2["children"] != "Bella":
            return False
        if house3["cigar"] == "prince" and house3["children"] != "Bella":
            return False
        if house1["phone_model"] == "iphone 13" and house2["phone_model"] != "samsung galaxy s21":
            return False
        if house2["phone_model"] == "iphone 13" and house3["phone_model"] != "samsung galaxy s21":
            return False
        if house1["children"] == "Fred" and house2["name"] != "Arnold":
            return False
        if house2["children"] == "Fred" and house3["name"] != "Arnold":
            return False
        if names.index("Peter") > names.index("Eric"):
            return False
        if house1["book_genre"] == "science fiction" or house2["book_genre"] == "science fiction":
            return False
        if house3["book_genre"] != "science fiction":
            return False
        if house2["book_genre"] == "mystery":
            return False

        return True

    # Iterate through all permutations to find the valid solution
    for perm in all_permutations:
        if is_valid_solution(perm):
            (name_order, cigar_order, animal_order, children_order, book_genre_order, phone_model_order) = perm
            solution = {
                "solution": {
                    "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                    "rows": [
                        ["1", name_order[0], cigar_order[0], animal_order[0], children_order[0], book_genre_order[0], phone_model_order[0]],
                        ["2", name_order[1], cigar_order[1], animal_order[1], children_order[1], book_genre_order[1], phone_model_order[1]],
                        ["3", name_order[2], cigar_order[2], animal_order[2], children_order[2], book_genre_order[2], phone_model_order[2]]
                    ]
                }
            }
            print(json.dumps(solution))
            return

# Solve the puzzle
solve_puzzle()