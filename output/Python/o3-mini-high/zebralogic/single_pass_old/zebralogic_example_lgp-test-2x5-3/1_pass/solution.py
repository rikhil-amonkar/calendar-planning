#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    book_genres = ["science fiction", "mystery"]
    music_genres = ["rock", "pop"]
    birthday_months = ["april", "sept"]

    # Iterate over all possible assignments using permutations.
    for name_perm in itertools.permutations(names):
        for hobby_perm in itertools.permutations(hobbies):
            for book_perm in itertools.permutations(book_genres):
                for music_perm in itertools.permutations(music_genres):
                    for bd_perm in itertools.permutations(birthday_months):
                        # Construct houses as dictionaries.
                        house1 = {
                            "House": "1",
                            "Name": name_perm[0],
                            "hobby": hobby_perm[0],
                            "favorite book genres": book_perm[0],
                            "favorite music genres": music_perm[0],
                            "birthday month": bd_perm[0]
                        }
                        house2 = {
                            "House": "2",
                            "Name": name_perm[1],
                            "hobby": hobby_perm[1],
                            "favorite book genres": book_perm[1],
                            "favorite music genres": music_perm[1],
                            "birthday month": bd_perm[1]
                        }
                        
                        # Constraint 5: The person who loves mystery books is in the first house.
                        if house1["favorite book genres"] != "mystery":
                            continue
                        
                        # Constraint 2: Arnold is not in the first house.
                        if house1["Name"] == "Arnold":
                            continue
                        
                        valid = True
                        # Check constraints for both houses.
                        for house in (house1, house2):
                            # Constraint 1: The person who loves mystery books is the person who loves rock music.
                            if house["favorite book genres"] == "mystery" and house["favorite music genres"] != "rock":
                                valid = False
                                break
                            # Constraint 3: The person who loves mystery books is the person who enjoys gardening.
                            if house["favorite book genres"] == "mystery" and house["hobby"] != "gardening":
                                valid = False
                                break
                            # Constraint 4: The person whose birthday is in April is Arnold.
                            if house["birthday month"] == "april" and house["Name"] != "Arnold":
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        header = ["House", "Name", "hobby", "favorite book genres", "favorite music genres", "birthday month"]
                        rows = [
                            [house1["House"], house1["Name"], house1["hobby"], house1["favorite book genres"], house1["favorite music genres"], house1["birthday month"]],
                            [house2["House"], house2["Name"], house2["hobby"], house2["favorite book genres"], house2["favorite music genres"], house2["birthday month"]]
                        ]
                        solution = {"solution": {"header": header, "rows": rows}}
                        print(json.dumps(solution))
                        return

if __name__ == "__main__":
    main()