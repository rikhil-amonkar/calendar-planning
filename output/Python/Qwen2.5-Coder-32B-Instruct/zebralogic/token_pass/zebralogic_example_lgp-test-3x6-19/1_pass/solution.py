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
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(cigars)) + \
                       list(itertools.permutations(animals)) + \
                       list(itertools.permutations(children)) + \
                       list(itertools.permutations(book_genres)) + \
                       list(itertools.permutations(phone_models))

    # Iterate over all possible combinations of permutations
    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            for animal_perm in itertools.permutations(animals):
                for child_perm in itertools.permutations(children):
                    for book_genre_perm in itertools.permutations(book_genres):
                        for phone_model_perm in itertools.permutations(phone_models):
                            # Create the houses with the current permutation
                            houses = [
                                {"Name": name_perm[0], "Cigar": cigar_perm[0], "Animal": animal_perm[0], "Children": child_perm[0], "BookGenre": book_genre_perm[0], "PhoneModel": phone_model_perm[0]},
                                {"Name": name_perm[1], "Cigar": cigar_perm[1], "Animal": animal_perm[1], "Children": child_perm[1], "BookGenre": book_genre_perm[1], "PhoneModel": phone_model_perm[1]},
                                {"Name": name_perm[2], "Cigar": cigar_perm[2], "Animal": animal_perm[2], "Children": child_perm[2], "BookGenre": book_genre_perm[2], "PhoneModel": phone_model_perm[2]}
                            ]

                            # Check all the clues
                            if (houses[book_genre_perm.index("mystery")]["Children"] == "Fred" and
                                houses[animal_perm.index("cat")]["Name"] == "Eric" and
                                houses[1]["Cigar"] == "pall mall" and
                                houses[child_perm.index("Meredith")]["Animal"] == "horse" and
                                houses[cigar_perm.index("prince")]["Children"] == "Bella" and
                                houses[phone_model_perm.index("iphone 13")]["PhoneModel"] == "iphone 13" and
                                houses[phone_model_perm.index("samsung galaxy s21")]["PhoneModel"] == "samsung galaxy s21" and
                                houses.index(houses[book_genre_perm.index("mystery")]) != 1 and
                                houses.index(houses[book_genre_perm.index("science fiction")]) == 2 and
                                houses.index(houses[children.index("Fred")]) == houses.index(houses[name_perm.index("Arnold")]) - 1 and
                                houses.index(houses[name_perm.index("Peter")]) < houses.index(houses[name_perm.index("Eric")])):
                                
                                # If all conditions are met, format the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                                        "rows": [
                                            ["1", houses[0]["Name"], houses[0]["Cigar"], houses[0]["Animal"], houses[0]["Children"], houses[0]["BookGenre"], houses[0]["PhoneModel"]],
                                            ["2", houses[1]["Name"], houses[1]["Cigar"], houses[1]["Animal"], houses[1]["Children"], houses[1]["BookGenre"], houses[1]["PhoneModel"]],
                                            ["3", houses[2]["Name"], houses[2]["Cigar"], houses[2]["Animal"], houses[2]["Children"], houses[2]["BookGenre"], houses[2]["PhoneModel"]]
                                        ]
                                    }
                                }
                                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())