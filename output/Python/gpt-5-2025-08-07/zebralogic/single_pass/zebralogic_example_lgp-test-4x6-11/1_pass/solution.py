import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4]

    Names = ["Peter", "Alice", "Eric", "Arnold"]
    Hobbies = ["cooking", "painting", "gardening", "photography"]
    Animals = ["horse", "fish", "cat", "bird"]
    BookGenres = ["fantasy", "mystery", "romance", "science fiction"]
    Birthdays = ["april", "jan", "sept", "feb"]
    MusicGenres = ["pop", "rock", "classical", "jazz"]

    solutions = []

    # Precompute permutations
    perms_books = []
    for book in permutations(BookGenres):
        # 4. The person who loves romance books is not in the fourth house.
        # 11. The painter is directly left of the romance books -> romance cannot be in house 1.
        idx_rom = book.index("romance")
        if idx_rom in (0, 3):  # not house 1 (index 0) or house 4 (index 3)
            continue
        perms_books.append(book)

    for book in perms_books:
        idx_rom = book.index("romance")
        idx_mystery = book.index("mystery")

        # Hobbies with constraints
        for hobby in permutations(Hobbies):
            # 1. cooking = romance
            if hobby.index("cooking") != idx_rom:
                continue
            # 11. painting is directly left of romance
            if hobby.index("painting") != idx_rom - 1:
                continue
            # 15. cooking not in the third house (index 2)
            if hobby.index("cooking") == 2:
                continue

            # Music with constraints
            for music in permutations(MusicGenres):
                # 9. jazz = cooking
                if music.index("jazz") != hobby.index("cooking"):
                    continue
                # 10. rock = mystery books
                if music.index("rock") != idx_mystery:
                    continue

                # Birthdays with constraints
                for bday in permutations(Birthdays):
                    # 14. rock is directly left of January
                    if bday.index("jan") != music.index("rock") + 1:
                        continue
                    # 8. gardening = April
                    if bday.index("april") != hobby.index("gardening"):
                        continue
                    # 2. February = pop music
                    if bday.index("feb") != music.index("pop"):
                        continue

                    # Animals with constraints
                    for animal in permutations(Animals):
                        # 5. February = fish
                        if animal.index("fish") != bday.index("feb"):
                            continue
                        # 7. horses = rock
                        if animal.index("horse") != music.index("rock"):
                            continue
                        # 16. cat to the right of horses
                        if not (animal.index("cat") > animal.index("horse")):
                            continue

                        # Names with constraints
                        for name in permutations(Names):
                            # 13. gardening = Arnold
                            if name.index("Arnold") != hobby.index("gardening"):
                                continue
                            # 12. Peter = pop
                            if name.index("Peter") != music.index("pop"):
                                continue
                            # 6. Alice right of fantasy
                            if not (name.index("Alice") > book.index("fantasy")):
                                continue
                            # 3. Eric not in second house (index 1)
                            if name[1] == "Eric":
                                continue

                            # Collect solution
                            sol = []
                            for i in range(4):
                                sol.append({
                                    "House": str(i + 1),
                                    "Name": name[i],
                                    "Hobby": hobby[i],
                                    "Animal": animal[i],
                                    "BookGenre": book[i],
                                    "Birthday": bday[i],
                                    "MusicGenre": music[i],
                                })
                            solutions.append(sol)

    # Assuming unique solution as typical for Zebra puzzles
    if not solutions:
        raise RuntimeError("No solution found.")
    solution = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": [
                [
                    row["House"],
                    row["Name"],
                    row["Hobby"],
                    row["Animal"],
                    row["BookGenre"],
                    row["Birthday"],
                    row["MusicGenre"],
                ]
                for row in solution
            ],
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()