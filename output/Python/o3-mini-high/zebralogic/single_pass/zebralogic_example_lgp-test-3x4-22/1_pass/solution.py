#!/usr/bin/env python3
import itertools
import json

def solve():
    # Attributes as given in the puzzle
    houses_numbers = [1, 2, 3]
    names_list = ["Arnold", "Eric", "Peter"]
    music_list = ["pop", "rock", "classical"]
    child_list = ["Fred", "Meredith", "Bella"]
    book_list = ["mystery", "romance", "science fiction"]

    # Iterate over every permutation of attributes
    for names_perm in itertools.permutations(names_list):
        # Clue 2: Peter is in the first house.
        if names_perm[0] != "Peter":
            continue
        for music_perm in itertools.permutations(music_list):
            for child_perm in itertools.permutations(child_list):
                for book_perm in itertools.permutations(book_list):
                    houses = []
                    for i in range(3):
                        houses.append({
                            "House": str(i+1),
                            "Name": names_perm[i],
                            "favorite music genres": music_perm[i],
                            "child": child_perm[i],
                            "favorite book genres": book_perm[i]
                        })
                    
                    valid = True

                    # Clue 1:
                    # "The person's child is named Fred is directly left of the person who loves mystery books."
                    fred_index = None
                    for idx, house in enumerate(houses):
                        if house["child"] == "Fred":
                            fred_index = idx
                    # Fred cannot be in the rightmost house and his immediate right neighbor must have mystery books.
                    if fred_index is None or fred_index == 2:
                        valid = False
                    else:
                        if houses[fred_index+1]["favorite book genres"] != "mystery":
                            valid = False
                    if not valid:
                        continue

                    # Clues 3 and 5:
                    # 3. "The person who loves mystery books is the person who loves classical music."
                    # 5. "Eric is the person who loves mystery books."
                    mystery_house = None
                    for house in houses:
                        if house["favorite book genres"] == "mystery":
                            mystery_house = house
                    if mystery_house is None or mystery_house["favorite music genres"] != "classical" or mystery_house["Name"] != "Eric":
                        valid = False
                    if not valid:
                        continue
                    # Also, if a house is occupied by Eric, his book genre must be mystery.
                    for house in houses:
                        if house["Name"] == "Eric" and house["favorite book genres"] != "mystery":
                            valid = False
                    if not valid:
                        continue

                    # Clue 4:
                    # "The person who loves science fiction books is the person's child is named Meredith."
                    for house in houses:
                        if house["favorite book genres"] == "science fiction" and house["child"] != "Meredith":
                            valid = False
                    if not valid:
                        continue

                    # Clue 6:
                    # "The person who loves rock music is somewhere to the right of the person who loves romance books."
                    romance_index = None
                    rock_index = None
                    for idx, house in enumerate(houses):
                        if house["favorite book genres"] == "romance":
                            romance_index = idx
                        if house["favorite music genres"] == "rock":
                            rock_index = idx
                    if romance_index is None or rock_index is None or rock_index <= romance_index:
                        valid = False
                    if not valid:
                        continue

                    # If all constraints are satisfied, output the solution.
                    header = ["House", "Name", "favorite music genres", "child", "favorite book genres"]
                    rows = [[house[attr] for attr in header] for house in houses]
                    output = {"solution": {"header": header, "rows": rows}}
                    print(json.dumps(output, indent=2))
                    return

if __name__ == "__main__":
    solve()