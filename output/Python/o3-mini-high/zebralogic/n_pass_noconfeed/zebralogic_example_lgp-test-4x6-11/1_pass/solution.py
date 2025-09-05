import json

def check_assigned(houses):
    """
    Checks the constraints for the current partially (or fully) assigned list of houses.
    Houses is a list of dictionaries representing houses in order.
    Only adjacent constraints and order constraints that can be checked with the assigned houses are verified.
    """
    n = len(houses)
    
    for i, house in enumerate(houses):
        # Constraint: If the person is Peter then birthday must be feb, animal fish, music pop.
        if house["Name"] == "Peter":
            if house["Birthday"] != "feb" or house["Animal"] != "fish" or house["MusicGenre"] != "pop":
                return False
        # Constraint: If the person is Arnold then hobby must be gardening and birthday must be april.
        if house["Name"] == "Arnold":
            if house["Hobby"] != "gardening" or house["Birthday"] != "april":
                return False
        # Constraint: The person who loves cooking is the one who loves romance books and jazz music.
        if house["Hobby"] == "cooking":
            if house["BookGenre"] != "romance" or house["MusicGenre"] != "jazz":
                return False
            # Cooking is not allowed in the third house (house index 2, i.e. House #3)
            if i == 2:
                return False
        # Constraint: The person who loves romance books is not in the fourth house.
        if house["BookGenre"] == "romance" and i == 3:
            return False
        # Constraint: The person who enjoys gardening has birthday in april.
        if house["Hobby"] == "gardening":
            if house["Birthday"] != "april":
                return False
        # Constraint: The person whose birthday is in feb must have pop music and keep fish.
        if house["Birthday"] == "feb":
            if house["MusicGenre"] != "pop" or house["Animal"] != "fish":
                return False
        # Constraint: The person who keeps horses must have rock music and mystery books.
        if house["Animal"] == "horse":
            if house["MusicGenre"] != "rock" or house["BookGenre"] != "mystery":
                return False
        # Constraint: Eric is not in the second house (index 1)
        if i == 1 and house["Name"] == "Eric":
            return False
        # For house 0, Alice cannot be there because she must be to the right of the fantasy lover.
        if i == 0 and house["Name"] == "Alice":
            return False
        # For house 0, if animal is cat then it violates "cat is to the right of horse"
        if i == 0 and house["Animal"] == "cat":
            return False

    # Adjacent constraints – only check for houses that have a right neighbor.
    for i in range(n - 1):
        # Clue 11: The person who paints is directly left of the person who loves romance books.
        if houses[i]["Hobby"] == "painting":
            if houses[i+1]["BookGenre"] != "romance":
                return False
        # Clue 14: The person with rock music is directly left of the person whose birthday is in jan.
        if houses[i]["MusicGenre"] == "rock":
            if houses[i+1]["Birthday"] != "jan":
                return False

    # Ordering constraints (nonadjacent):
    # Clue 6: Alice is somewhere to the right of the person who loves fantasy books.
    for i, house in enumerate(houses):
        if house["Name"] == "Alice":
            found = False
            for j in range(i):
                if houses[j]["BookGenre"] == "fantasy":
                    found = True
                    break
            if not found:
                return False

    # Clue 16: The cat lover is somewhere to the right of the person who keeps horses.
    for i, house in enumerate(houses):
        if house["Animal"] == "cat":
            found = False
            for j in range(i):
                if houses[j]["Animal"] == "horse":
                    found = True
                    break
            if not found:
                return False

    return True

def backtrack(i, houses, rem_names, rem_hobbies, rem_animals, rem_books, rem_birthdays, rem_music):
    """
    Recursively assign values to each house (houses 0 to 3) from the remaining sets.
    houses: list of already assigned house dictionaries.
    i: current house index to assign.
    rem_*: remaining available values for each attribute.
    Returns a complete valid assignment (list of houses) if found, otherwise None.
    """
    if i == 4:
        # All houses assigned; final check of constraints.
        if check_assigned(houses):
            return houses
        return None

    for name in list(rem_names):
        for hobby in list(rem_hobbies):
            for animal in list(rem_animals):
                for book in list(rem_books):
                    for birthday in list(rem_birthdays):
                        for music in list(rem_music):
                            candidate = {
                                "Name": name,
                                "Hobby": hobby,
                                "Animal": animal,
                                "BookGenre": book,
                                "Birthday": birthday,
                                "MusicGenre": music
                            }
                            # Forced constraints:
                            if name == "Peter":
                                # Peter must have pop music, feb birthday, and fish.
                                if birthday != "feb" or music != "pop" or animal != "fish":
                                    continue
                            if name == "Arnold":
                                # Arnold must have gardening and april birthday.
                                if hobby != "gardening" or birthday != "april":
                                    continue
                            if hobby == "cooking":
                                # Cooking implies romance books and jazz.
                                if book != "romance" or music != "jazz":
                                    continue
                                # Cooking cannot be in the third house (house #3, index 2)
                                if i == 2:
                                    continue
                            if book == "romance" and i == 3:
                                # Romance books not allowed in the fourth house.
                                continue
                            if hobby == "gardening":
                                if birthday != "april":
                                    continue
                            if animal == "horse":
                                # Horse keeper must have rock music and mystery books.
                                if music != "rock" or book != "mystery":
                                    continue
                            if birthday == "feb":
                                # Feb birthday must come with pop music and fish.
                                if music != "pop" or animal != "fish":
                                    continue
                            if i == 1 and name == "Eric":
                                # Eric is not allowed in the second house.
                                continue
                            if i == 3 and music == "rock":
                                # Can't place rock in the fourth house because it must be immediately left of jan.
                                continue

                            # Check adjacent constraint relative to previous house.
                            if i > 0:
                                prev = houses[i - 1]
                                if prev["Hobby"] == "painting" and book != "romance":
                                    continue
                                if prev["MusicGenre"] == "rock" and birthday != "jan":
                                    continue

                            new_houses = houses + [candidate]
                            if not check_assigned(new_houses):
                                continue

                            new_rem_names = rem_names - {name}
                            new_rem_hobbies = rem_hobbies - {hobby}
                            new_rem_animals = rem_animals - {animal}
                            new_rem_books = rem_books - {book}
                            new_rem_birthdays = rem_birthdays - {birthday}
                            new_rem_music = rem_music - {music}

                            result = backtrack(i + 1, new_houses, new_rem_names, new_rem_hobbies,
                                               new_rem_animals, new_rem_books, new_rem_birthdays, new_rem_music)
                            if result is not None:
                                return result
    return None

def solve_puzzle():
    # Define the domains for each characteristic.
    names = {"Peter", "Alice", "Eric", "Arnold"}
    hobbies = {"cooking", "painting", "gardening", "photography"}
    animals = {"horse", "fish", "cat", "bird"}
    books = {"fantasy", "mystery", "romance", "science fiction"}
    birthdays = {"april", "jan", "sept", "feb"}
    music = {"pop", "rock", "classical", "jazz"}
    
    solution = backtrack(0, [], names, hobbies, animals, books, birthdays, music)
    return solution

def main():
    sol = solve_puzzle()
    if sol is None:
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                "rows": []
            }
        }
    else:
        rows = []
        # Houses are numbered 1 to 4.
        for i, house in enumerate(sol):
            row = [
                str(i + 1),
                house["Name"],
                house["Hobby"],
                house["Animal"],
                house["BookGenre"],
                house["Birthday"],
                house["MusicGenre"]
            ]
            rows.append(row)
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                "rows": rows
            }
        }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()