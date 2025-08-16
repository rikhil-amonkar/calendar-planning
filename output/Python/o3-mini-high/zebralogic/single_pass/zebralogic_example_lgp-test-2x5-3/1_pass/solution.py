#!/usr/bin/env python3
import itertools
import json

def solve():
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    book_genres = ["science fiction", "mystery"]
    music_genres = ["rock", "pop"]
    birthdays = ["april", "sept"]

    for name_perm in itertools.permutations(names):
        for hobby_perm in itertools.permutations(hobbies):
            for book_perm in itertools.permutations(book_genres):
                for music_perm in itertools.permutations(music_genres):
                    for birthday_perm in itertools.permutations(birthdays):
                        # Build assignments for each house as a list of dictionaries
                        assignment = []
                        for i in range(len(houses)):
                            house = {
                                "House": str(houses[i]),
                                "Name": name_perm[i],
                                "Hobby": hobby_perm[i],
                                "BookGenre": book_perm[i],
                                "MusicGenre": music_perm[i],
                                "Birthday": birthday_perm[i]
                            }
                            assignment.append(house)
                        # Constraint 5: The person who loves mystery books is in the first house.
                        if assignment[0]["BookGenre"] != "mystery":
                            continue
                        # Constraint 1: The person who loves mystery books is the person who loves rock music.
                        valid = True
                        for house in assignment:
                            if house["BookGenre"] == "mystery" and house["MusicGenre"] != "rock":
                                valid = False
                                break
                            if house["MusicGenre"] == "rock" and house["BookGenre"] != "mystery":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 3: The person who loves mystery books is the person who enjoys gardening.
                        for house in assignment:
                            if house["BookGenre"] == "mystery" and house["Hobby"] != "gardening":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 2: Arnold is not in the first house.
                        if assignment[0]["Name"] == "Arnold":
                            continue
                        # Constraint 4: The person whose birthday is in April is Arnold.
                        for house in assignment:
                            if house["Birthday"] == "april" and house["Name"] != "Arnold":
                                valid = False
                                break
                        if not valid:
                            continue
                        # If all constraints are satisfied, return the solution.
                        return assignment
    return None

def main():
    solution_assignment = solve()
    header = ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"]
    rows = []
    if solution_assignment:
        for house in solution_assignment:
            row = [house[attr] for attr in header]
            rows.append(row)
    output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output))

if __name__ == "__main__":
    main()