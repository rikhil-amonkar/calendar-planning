import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Peter", "Alice", "Eric", "Arnold"]
    hobbies = ["cooking", "painting", "gardening", "photography"]
    animals = ["horse", "fish", "cat", "bird"]
    book_genres = ["fantasy", "mystery", "romance", "science fiction"]
    birthdays = ["april", "jan", "sept", "feb"]
    music_genres = ["pop", "rock", "classical", "jazz"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(names))
    all_permutations += list(itertools.permutations(hobbies))
    all_permutations += list(itertools.permutations(animals))
    all_permutations += list(itertools.permutations(book_genres))
    all_permutations += list(itertools.permutations(birthdays))
    all_permutations += list(itertools.permutations(music_genres))

    # Check all combinations
    for name_perm in all_permutations[:24]:
        for hobby_perm in all_permutations[24:48]:
            for animal_perm in all_permutations[48:72]:
                for book_genre_perm in all_permutations[72:96]:
                    for birthday_perm in all_permutations[96:120]:
                        for music_genre_perm in all_permutations[120:144]:
                            if (
                                # Clue 1
                                hobby_perm.index("cooking") == book_genre_perm.index("romance") and
                                # Clue 2
                                birthday_perm.index("feb") == music_genre_perm.index("pop") and
                                # Clue 3
                                name_perm.index("Eric") != 1 and
                                # Clue 4
                                book_genre_perm.index("romance") != 3 and
                                # Clue 5
                                birthday_perm.index("feb") == animal_perm.index("fish") and
                                # Clue 6
                                name_perm.index("Alice") > book_genre_perm.index("fantasy") and
                                # Clue 7
                                animal_perm.index("horse") == music_genre_perm.index("rock") and
                                # Clue 8
                                hobby_perm.index("gardening") == birthday_perm.index("april") and
                                # Clue 9
                                music_genre_perm.index("jazz") == hobby_perm.index("cooking") and
                                # Clue 10
                                music_genre_perm.index("rock") == book_genre_perm.index("mystery") and
                                # Clue 11
                                hobby_perm.index("painting") + 1 == book_genre_perm.index("romance") and
                                # Clue 12
                                name_perm.index("Peter") == music_genre_perm.index("pop") and
                                # Clue 13
                                name_perm.index("Arnold") == hobby_perm.index("gardening") and
                                # Clue 14
                                music_genre_perm.index("rock") + 1 == birthday_perm.index("jan") and
                                # Clue 15
                                hobby_perm.index("cooking") != 2 and
                                # Clue 16
                                animal_perm.index("cat") > animal_perm.index("horse")
                            ):
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                                        "rows": []
                                    }
                                }
                                for i in range(4):
                                    solution["solution"]["rows"].append([
                                        str(i + 1),
                                        name_perm[i],
                                        hobby_perm[i],
                                        animal_perm[i],
                                        book_genre_perm[i],
                                        birthday_perm[i],
                                        music_genre_perm[i]
                                    ])
                                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())