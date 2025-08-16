#!/usr/bin/env python3
import json
import sys

# Define the six attribute lists
NAMES = ["Peter", "Alice", "Eric", "Arnold"]
HOBBIES = ["cooking", "painting", "gardening", "photography"]
ANIMALS = ["horse", "fish", "cat", "bird"]
BOOK_GENRES = ["fantasy", "mystery", "romance", "science fiction"]
BIRTHDAYS = ["april", "jan", "sept", "feb"]
MUSIC_GENRES = ["pop", "rock", "classical", "jazz"]

# The valid() function checks all constraints on the current (partial or full) assignment.
def valid(houses):
    # houses is a list of dicts, each dict has keys: Name, Hobby, Animal, BookGenre, Birthday, MusicGenre.
    n = len(houses)
    # Check constraints that apply per house.
    for i, house in enumerate(houses):
        # Constraint 1: Cooking and romance books go together.
        if house["Hobby"] == "cooking":
            if house["BookGenre"] != "romance":
                return False
        if house["BookGenre"] == "romance":
            if house["Hobby"] != "cooking":
                return False

        # Constraint 2: February birthday <-> pop music.
        if house["Birthday"] == "feb":
            if house["MusicGenre"] != "pop":
                return False
        if house["MusicGenre"] == "pop":
            if house["Birthday"] != "feb":
                return False

        # Constraint 3: Eric is not in the second house (index 1).
        if i == 1 and house["Name"] == "Eric":
            return False

        # Constraint 4: The person who loves romance books is not in the fourth house (index 3).
        if i == 3 and house["BookGenre"] == "romance":
            return False

        # Constraint 5: February birthday <-> fish keeper.
        if house["Birthday"] == "feb":
            if house["Animal"] != "fish":
                return False
        if house["Animal"] == "fish":
            if house["Birthday"] != "feb":
                return False

        # Constraint 7: Horses <-> rock music.
        if house["Animal"] == "horse":
            if house["MusicGenre"] != "rock":
                return False
        if house["MusicGenre"] == "rock":
            if house["Animal"] != "horse":
                return False

        # Constraint 8: Gardening <-> birthday in April.
        if house["Hobby"] == "gardening":
            if house["Birthday"] != "april":
                return False
        if house["Birthday"] == "april":
            if house["Hobby"] != "gardening":
                return False

        # Constraint 9: Jazz <-> cooking.
        if house["MusicGenre"] == "jazz":
            if house["Hobby"] != "cooking":
                return False
        if house["Hobby"] == "cooking":
            if house["MusicGenre"] != "jazz":
                return False

        # Constraint 10: Rock music <-> mystery books.
        if house["MusicGenre"] == "rock":
            if house["BookGenre"] != "mystery":
                return False
        if house["BookGenre"] == "mystery":
            if house["MusicGenre"] != "rock":
                return False

        # Constraint 12: Peter is the person who loves pop music.
        if house["Name"] == "Peter":
            if house["MusicGenre"] != "pop":
                return False
        if house["MusicGenre"] == "pop":
            if house["Name"] != "Peter":
                return False

        # Constraint 13: The person who enjoys gardening is Arnold.
        if house["Hobby"] == "gardening":
            if house["Name"] != "Arnold":
                return False
        if house["Name"] == "Arnold":
            if house["Hobby"] != "gardening":
                return False

        # Constraint 15: The person who loves cooking is not in the third house (index 2).
        if i == 2 and house["Hobby"] == "cooking":
            return False

    # Constraint 11: The person who paints is directly left of the person who loves romance books.
    # Check for every adjacent pair that is assigned.
    for i in range(n - 1):
        left = houses[i]
        right = houses[i+1]
        # If right has romance, left must paint.
        if right["BookGenre"] == "romance":
            if left["Hobby"] != "painting":
                return False
        # Conversely, if left is painting then right must be romance.
        if left["Hobby"] == "painting":
            if right["BookGenre"] != "romance":
                return False

    # Constraint 14: The person who loves rock music is directly left of the person whose birthday is in January.
    for i in range(n - 1):
        left = houses[i]
        right = houses[i+1]
        if left["MusicGenre"] == "rock":
            if right["Birthday"] != "jan":
                return False
        if right["Birthday"] == "jan":
            if left["MusicGenre"] != "rock":
                return False

    # Constraint 6: Alice is somewhere to the right of the person who loves fantasy books.
    alice_index = None
    fantasy_index = None
    for i, house in enumerate(houses):
        if house["Name"] == "Alice":
            alice_index = i
        if house["BookGenre"] == "fantasy":
            fantasy_index = i
    if (alice_index is not None) and (fantasy_index is not None):
        if alice_index <= fantasy_index:
            return False

    # Constraint 16: The cat lover is somewhere to the right of the person who keeps horses.
    cat_index = None
    horse_index = None
    for i, house in enumerate(houses):
        if house["Animal"] == "cat":
            cat_index = i
        if house["Animal"] == "horse":
            horse_index = i
    if (cat_index is not None) and (horse_index is not None):
        if cat_index <= horse_index:
            return False

    return True

# Backtracking search: assign houses one by one.
def backtrack(i, houses, rem_names, rem_hobbies, rem_animals, rem_books, rem_birthdays, rem_music):
    if i == 4:
        # All houses assigned, check global constraints one more time.
        if valid(houses):
            return houses
        return None
    # Try all combinations for the ith house from the remaining values.
    for name in rem_names:
        for hobby in rem_hobbies:
            for animal in rem_animals:
                for book in rem_books:
                    for birthday in rem_birthdays:
                        for music in rem_music:
                            house = {
                                "Name": name,
                                "Hobby": hobby,
                                "Animal": animal,
                                "BookGenre": book,
                                "Birthday": birthday,
                                "MusicGenre": music
                            }
                            houses.append(house)
                            if valid(houses):
                                # Prepare new remaining lists without the used values.
                                new_rem_names = [x for x in rem_names if x != name]
                                new_rem_hobbies = [x for x in rem_hobbies if x != hobby]
                                new_rem_animals = [x for x in rem_animals if x != animal]
                                new_rem_books = [x for x in rem_books if x != book]
                                new_rem_birthdays = [x for x in rem_birthdays if x != birthday]
                                new_rem_music = [x for x in rem_music if x != music]
                                result = backtrack(i+1, houses, new_rem_names, new_rem_hobbies, new_rem_animals, new_rem_books, new_rem_birthdays, new_rem_music)
                                if result is not None:
                                    return result
                            houses.pop()
    return None

def main():
    solution = backtrack(0, [], NAMES, HOBBIES, ANIMALS, BOOK_GENRES, BIRTHDAYS, MUSIC_GENRES)
    if solution is None:
        result = {"solution": {"header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                                 "rows": []}}
    else:
        # Build rows in order: house numbers 1 to 4
        rows = []
        for i, house in enumerate(solution):
            row = [
                str(i+1),
                house["Name"],
                house["Hobby"],
                house["Animal"],
                house["BookGenre"],
                house["Birthday"],
                house["MusicGenre"]
            ]
            rows.append(row)
        result = {"solution": {"header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                               "rows": rows}}
    # Output JSON.
    print(json.dumps(result))

if __name__ == '__main__':
    sys.exit(main())