#!/usr/bin/env python3
import itertools
import json

def main():
    names_list = ["Peter", "Alice", "Eric", "Arnold"]
    hobbies_list = ["cooking", "painting", "gardening", "photography"]
    animals_list = ["horse", "fish", "cat", "bird"]
    books_list = ["fantasy", "romance", "mystery", "science fiction"]
    birthdays_list = ["april", "jan", "sept", "feb"]
    music_list = ["pop", "rock", "classical", "jazz"]

    # We'll iterate over all permutations of the attribute lists.
    for names in itertools.permutations(names_list):
        # Constraint: Eric is not in the second house (index 1)
        if names[1] == "Eric":
            continue

        for hobbies in itertools.permutations(hobbies_list):
            # Constraint: Arnold must enjoy gardening.
            arnold_index = names.index("Arnold")
            if hobbies[arnold_index] != "gardening":
                continue
            # Constraint: Cooking is not in the third house (house index 2).
            if hobbies[2] == "cooking":
                continue
            # Constraint: The person who paints (hobby "painting") must have a right‐neighbor.
            if hobbies[3] == "painting":
                continue

            for music in itertools.permutations(music_list):
                # Constraint: Peter loves pop music.
                peter_index = names.index("Peter")
                if music[peter_index] != "pop":
                    continue
                # Constraint: The person who loves cooking must love jazz music.
                if "cooking" in hobbies:
                    cook_index = hobbies.index("cooking")
                    if music[cook_index] != "jazz":
                        continue
                # Additional check: The person who loves jazz music must be the one who loves cooking.
                valid_jazz = True
                for i in range(4):
                    if music[i] == "jazz" and hobbies[i] != "cooking":
                        valid_jazz = False
                        break
                if not valid_jazz:
                    continue
                # Constraint: If a house has pop music, its birthday must be February and vice‐versa.
                # (Will check this once birthdays are assigned.)
                # Constraint: If music is rock, it cannot be in the last house because it must be immediately left of a house.
                if any(i == 3 and music[i] == "rock" for i in range(4)):
                    continue

                for birthdays in itertools.permutations(birthdays_list):
                    # Constraint: The person enjoying gardening must have birthday in April.
                    if birthdays[arnold_index] != "april":
                        continue
                    # Constraint: Houses with pop music must have birthday feb and vice‐versa.
                    valid_pop = True
                    for i in range(4):
                        if music[i] == "pop" and birthdays[i] != "feb":
                            valid_pop = False
                            break
                        if birthdays[i] == "feb" and music[i] != "pop":
                            valid_pop = False
                            break
                    if not valid_pop:
                        continue
                    # Constraint: Any house with rock music must be immediately followed (to its right) by a house with birthday jan.
                    valid_rock_bday = True
                    for i in range(3):
                        if music[i] == "rock":
                            if birthdays[i+1] != "jan":
                                valid_rock_bday = False
                                break
                    if not valid_rock_bday:
                        continue

                    for animals in itertools.permutations(animals_list):
                        # Constraint: The person whose birthday is in February must keep fish, and vice‐versa.
                        valid_fish = True
                        for i in range(4):
                            if birthdays[i] == "feb" and animals[i] != "fish":
                                valid_fish = False
                                break
                            if animals[i] == "fish" and birthdays[i] != "feb":
                                valid_fish = False
                                break
                        if not valid_fish:
                            continue
                        # Constraint: The person who keeps horses must love rock music, and vice‐versa.
                        valid_horse = True
                        for i in range(4):
                            if music[i] == "rock" and animals[i] != "horse":
                                valid_horse = False
                                break
                            if animals[i] == "horse" and music[i] != "rock":
                                valid_horse = False
                                break
                        if not valid_horse:
                            continue
                        # Constraint: The cat lover is somewhere to the right of the person who keeps horses.
                        if "horse" in animals:
                            horse_index = animals.index("horse")
                            if not any(animals[j] == "cat" for j in range(horse_index + 1, 4)):
                                continue

                        for books in itertools.permutations(books_list):
                            # Constraint: The person with the cooking hobby must love romance books.
                            if "cooking" in hobbies:
                                cook_index = hobbies.index("cooking")
                                if books[cook_index] != "romance":
                                    continue
                            # Constraint: The person who loves rock music must love mystery books, and vice‐versa.
                            valid_rock_book = True
                            for i in range(4):
                                if music[i] == "rock" and books[i] != "mystery":
                                    valid_rock_book = False
                                    break
                                if books[i] == "mystery" and music[i] != "rock":
                                    valid_rock_book = False
                                    break
                            if not valid_rock_book:
                                continue
                            # Constraint: The person who loves romance books is not in the fourth house.
                            if books[3] == "romance":
                                continue
                            # Constraint: The person who paints (hobby "painting") is directly left of the person who loves romance books.
                            painting_index = hobbies.index("painting")
                            if painting_index == 3:
                                continue
                            if books[painting_index + 1] != "romance":
                                continue
                            # Constraint: Alice is somewhere to the right of the person who loves fantasy books.
                            fantasy_index = books.index("fantasy")
                            alice_index = names.index("Alice")
                            if alice_index <= fantasy_index:
                                continue
                            
                            # All constraints are satisfied. Construct the solution.
                            header = ["House", "Name", "hobby", "animal", "book", "birthday", "music"]
                            rows = []
                            for i in range(4):
                                row = [str(i+1), names[i], hobbies[i], animals[i], books[i], birthdays[i], music[i]]
                                rows.append(row)
                            output = {"solution": {"header": header, "rows": rows}}
                            print(json.dumps(output))
                            return

if __name__ == "__main__":
    main()