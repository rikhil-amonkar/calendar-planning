import itertools
import json

def solve():
    houses_count = 3
    names = ["Peter", "Arnold", "Eric"]
    book_genres = ["science fiction", "mystery", "romance"]
    smoothies = ["watermelon", "desert", "cherry"]
    birthdays = ["april", "jan", "sept"]
    heights = ["average", "very short", "short"]

    # Iterate through permutations of each category
    for names_perm in itertools.permutations(names):
        # Clue 7: Eric is in the first house.
        if names_perm[0] != "Eric":
            continue

        for book_perm in itertools.permutations(book_genres):
            # Clue 2: Arnold is the person who loves mystery books.
            valid = True
            for i in range(houses_count):
                if names_perm[i] == "Arnold" and book_perm[i] != "mystery":
                    valid = False
                    break
            if not valid:
                continue

            for smoothie_perm in itertools.permutations(smoothies):
                # Clue 9: The Watermelon smoothie lover is Eric.
                try:
                    idx_watermelon = smoothie_perm.index("watermelon")
                except ValueError:
                    continue
                if names_perm[idx_watermelon] != "Eric":
                    continue

                # Clue 1: The person who likes Cherry smoothies is not in the second house.
                if smoothie_perm[1] == "cherry":
                    continue

                for birthday_perm in itertools.permutations(birthdays):
                    # Clue 3: The person whose birthday is in January is not in the first house.
                    if birthday_perm[0] == "jan":
                        continue

                    for height_perm in itertools.permutations(heights):
                        valid = True

                        # Clue 4: The person who is very short is the person who loves romance books.
                        try:
                            idx_very_short = height_perm.index("very short")
                        except ValueError:
                            valid = False
                        else:
                            if book_perm[idx_very_short] != "romance":
                                valid = False

                        # Clue 5: The person who loves mystery books is the person whose birthday is in September.
                        for i in range(houses_count):
                            if book_perm[i] == "mystery" and birthday_perm[i] != "sept":
                                valid = False
                                break

                        # Clue 6: The person who has an average height is the Desert smoothie lover.
                        try:
                            idx_average = height_perm.index("average")
                        except ValueError:
                            valid = False
                        else:
                            if smoothie_perm[idx_average] != "desert":
                                valid = False

                        # Clue 8: The Watermelon smoothie lover is the person who is short.
                        if height_perm[idx_watermelon] != "short":
                            valid = False

                        if not valid:
                            continue

                        # All constraints satisfied: Build the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                                "rows": []
                            }
                        }
                        for i in range(houses_count):
                            row = [
                                str(i + 1),
                                names_perm[i],
                                book_perm[i],
                                smoothie_perm[i],
                                birthday_perm[i],
                                height_perm[i]
                            ]
                            solution["solution"]["rows"].append(row)
                        print(json.dumps(solution, indent=2))
                        return

if __name__ == '__main__':
    solve()