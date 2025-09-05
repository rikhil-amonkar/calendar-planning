import itertools
import json

def main():
    names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
    book_genres = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
    occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

    # We'll iterate over possible assignments with permutations and use constraints to prune the search.
    for names_perm in itertools.permutations(names):
        # Clue 12: Eric is in the third house (index 2)
        if names_perm[2] != "Eric":
            continue
        # Clue 5: Bob is not in the fifth house (index 4)
        if names_perm[4] == "Bob":
            continue
        # Clue 13: The person who loves mystery (Carol) is not in the fifth house (index 4)
        if names_perm[4] == "Carol":
            continue
        # Clue 2: Bob and the person who loves mystery books (Carol per Clue 3) are next to each other
        if abs(names_perm.index("Bob") - names_perm.index("Carol")) != 1:
            continue

        for occ_perm in itertools.permutations(occupations):
            # Clue 10: The person who is a doctor is in the first house (index 0)
            if occ_perm[0] != "doctor":
                continue
            # Clue 4 & Clue 1: The person who loves fantasy must be a lawyer, and Alice loves fantasy.
            # So the house with Alice must have occupation lawyer.
            alice_index = names_perm.index("Alice")
            if occ_perm[alice_index] != "lawyer":
                continue
            # Clue 7: The person who is a nurse is directly left of Alice.
            if alice_index == 0 or occ_perm[alice_index - 1] != "nurse":
                continue
            # Clue 6: Arnold is somewhere to the left of the person who is an engineer.
            if names_perm.index("Arnold") >= occ_perm.index("engineer"):
                continue

            for genre_perm in itertools.permutations(book_genres):
                # Clue 1: Alice loves fantasy.
                if genre_perm[alice_index] != "fantasy":
                    continue
                # Clue 3: Carol loves mystery.
                if genre_perm[names_perm.index("Carol")] != "mystery":
                    continue

                valid = True
                # Clues relating book genres and occupations for each house:
                for i in range(6):
                    # Clue 8: The person who loves biography books is the person who is a teacher.
                    if genre_perm[i] == "biography" and occ_perm[i] != "teacher":
                        valid = False
                        break
                    if occ_perm[i] == "teacher" and genre_perm[i] != "biography":
                        valid = False
                        break
                    # Clue 11: The person who loves science fiction is the person who is an artist.
                    if genre_perm[i] == "science fiction" and occ_perm[i] != "artist":
                        valid = False
                        break
                    if occ_perm[i] == "artist" and genre_perm[i] != "science fiction":
                        valid = False
                        break
                    # Clue 4 revisited: The person who is a lawyer is the person who loves fantasy.
                    if genre_perm[i] == "fantasy" and occ_perm[i] != "lawyer":
                        valid = False
                        break
                    if occ_perm[i] == "lawyer" and genre_perm[i] != "fantasy":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 9: The person who loves historical fiction is somewhere to the left of the person who is a teacher.
                teacher_index = occ_perm.index("teacher")
                hist_index = genre_perm.index("historical fiction")
                if hist_index >= teacher_index:
                    continue

                # All constraints satisfied. Build the solution output.
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Occupation"],
                        "rows": [
                            [str(i+1), names_perm[i], genre_perm[i], occ_perm[i]] for i in range(6)
                        ]
                    }
                }
                print(json.dumps(solution))
                return

if __name__ == "__main__":
    main()