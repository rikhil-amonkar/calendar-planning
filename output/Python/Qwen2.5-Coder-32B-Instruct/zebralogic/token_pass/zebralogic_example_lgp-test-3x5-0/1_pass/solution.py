import itertools
import json

def solve_puzzle():
    # Define possible values for each attribute
    names = ["Peter", "Arnold", "Eric"]
    book_genres = ["science fiction", "mystery", "romance"]
    smoothies = ["watermelon", "desert", "cherry"]
    birthdays = ["april", "jan", "sept"]
    heights = ["average", "very short", "short"]

    # Generate all possible permutations of attributes
    all_permutations = list(itertools.permutations(names)) * 2
    all_permutations.extend(list(itertools.permutations(book_genres)))
    all_permutations.extend(list(itertools.permutations(smoothies)))
    all_permutations.extend(list(itertools.permutations(birthdays)))
    all_permutations.extend(list(itertools.permutations(heights)))

    # Filter permutations based on constraints
    def is_valid_solution(houses):
        # Unpack houses
        house1, house2, house3 = houses

        # Constraint 1: The person who likes Cherry smoothies is not in the second house.
        if house2["Smoothie"] == "cherry":
            return False

        # Constraint 2: Arnold is the person who loves mystery books.
        if house1["Name"] == "Arnold" and house1["BookGenre"] != "mystery":
            return False
        if house2["Name"] == "Arnold" and house2["BookGenre"] != "mystery":
            return False
        if house3["Name"] == "Arnold" and house3["BookGenre"] != "mystery":
            return False

        # Constraint 3: The person whose birthday is in January is not in the first house.
        if house1["Birthday"] == "jan":
            return False

        # Constraint 4: The person who is very short is the person who loves romance books.
        if house1["Height"] == "very short" and house1["BookGenre"] != "romance":
            return False
        if house2["Height"] == "very short" and house2["BookGenre"] != "romance":
            return False
        if house3["Height"] == "very short" and house3["BookGenre"] != "romance":
            return False

        # Constraint 5: The person who loves mystery books is the person whose birthday is in September.
        if house1["BookGenre"] == "mystery" and house1["Birthday"] != "sept":
            return False
        if house2["BookGenre"] == "mystery" and house2["Birthday"] != "sept":
            return False
        if house3["BookGenre"] == "mystery" and house3["Birthday"] != "sept":
            return False

        # Constraint 6: The person who has an average height is the Desert smoothie lover.
        if house1["Height"] == "average" and house1["Smoothie"] != "desert":
            return False
        if house2["Height"] == "average" and house2["Smoothie"] != "desert":
            return False
        if house3["Height"] == "average" and house3["Smoothie"] != "desert":
            return False

        # Constraint 7: Eric is in the first house.
        if house1["Name"] != "Eric":
            return False

        # Constraint 8: The Watermelon smoothie lover is the person who is short.
        if house1["Smoothie"] == "watermelon" and house1["Height"] != "short":
            return False
        if house2["Smoothie"] == "watermelon" and house2["Height"] != "short":
            return False
        if house3["Smoothie"] == "watermelon" and house3["Height"] != "short":
            return False

        # Constraint 9: The Watermelon smoothie lover is Eric.
        if house1["Smoothie"] == "watermelon" and house1["Name"] != "Eric":
            return False
        if house2["Smoothie"] == "watermelon" and house2["Name"] != "Eric":
            return False
        if house3["Smoothie"] == "watermelon" and house3["Name"] != "Eric":
            return False

        return True

    # Generate all possible assignments of attributes to houses
    for name_perm in itertools.permutations(names):
        for genre_perm in itertools.permutations(book_genres):
            for smoothie_perm in itertools.permutations(smoothies):
                for birthday_perm in itertools.permutations(birthdays):
                    for height_perm in itertools.permutations(heights):
                        houses = [
                            {"Name": name_perm[0], "BookGenre": genre_perm[0], "Smoothie": smoothie_perm[0], "Birthday": birthday_perm[0], "Height": height_perm[0]},
                            {"Name": name_perm[1], "BookGenre": genre_perm[1], "Smoothie": smoothie_perm[1], "Birthday": birthday_perm[1], "Height": height_perm[1]},
                            {"Name": name_perm[2], "BookGenre": genre_perm[2], "Smoothie": smoothie_perm[2], "Birthday": birthday_perm[2], "Height": height_perm[2]}
                        ]
                        if is_valid_solution(houses):
                            # Format the solution as required
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                                    "rows": [
                                        ["1", houses[0]["Name"], houses[0]["BookGenre"], houses[0]["Smoothie"], houses[0]["Birthday"], houses[0]["Height"]],
                                        ["2", houses[1]["Name"], houses[1]["BookGenre"], houses[1]["Smoothie"], houses[1]["Birthday"], houses[1]["Height"]],
                                        ["3", houses[2]["Name"], houses[2]["BookGenre"], houses[2]["Smoothie"], houses[2]["Birthday"], houses[2]["Height"]]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())