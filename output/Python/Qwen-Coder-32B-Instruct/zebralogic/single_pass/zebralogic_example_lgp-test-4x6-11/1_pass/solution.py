import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Peter", "Alice", "Eric", "Arnold"]
    hobbies = ["cooking", "painting", "gardening", "photography"]
    animals = ["horse", "fish", "cat", "bird"]
    books = ["fantasy", "mystery", "romance", "science fiction"]
    birthdays = ["april", "jan", "sept", "feb"]
    musics = ["pop", "rock", "classical", "jazz"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(range(4)))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(name_perm, hobby_perm, animal_perm, book_perm, birthday_perm, music_perm):
        # Unpack permutations for easier access
        p, a, e, r = range(4)
        name_p, hobby_p, animal_p, book_p, birthday_p, music_p = name_perm, hobby_perm, animal_perm, book_perm, birthday_perm, music_perm

        # Apply each clue
        if hobby_p.index("cooking") != book_p.index("romance"):
            return False
        if birthday_p.index("feb") != music_p.index("pop"):
            return False
        if name_p[e] == 1:
            return False
        if book_p.index("romance") == 3:
            return False
        if birthday_p.index("feb") != animal_p.index("fish"):
            return False
        if name_p.index("Alice") <= book_p.index("fantasy"):
            return False
        if animal_p.index("horse") != music_p.index("rock"):
            return False
        if hobby_p.index("gardening") != birthday_p.index("april"):
            return False
        if music_p.index("jazz") != hobby_p.index("cooking"):
            return False
        if music_p.index("rock") != book_p.index("mystery"):
            return False
        if hobby_p.index("painting") + 1 != book_p.index("romance"):
            return False
        if name_p[p] != music_p.index("pop"):
            return False
        if name_p[a] != hobby_p.index("gardening"):
            return False
        if music_p.index("rock") + 1 != birthday_p.index("jan"):
            return False
        if hobby_p.index("cooking") == 2:
            return False
        if animal_p.index("cat") <= animal_p.index("horse"):
            return False

        return True

    # Iterate over all permutations to find a valid solution
    for name_perm in all_permutations:
        for hobby_perm in all_permutations:
            for animal_perm in all_permutations:
                for book_perm in all_permutations:
                    for birthday_perm in all_permutations:
                        for music_perm in all_permutations:
                            if is_valid_solution(name_perm, hobby_perm, animal_perm, book_perm, birthday_perm, music_perm):
                                # Construct the solution in the required format
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Hobby", "Animal", "Book", "Birthday", "Music"],
                                        "rows": []
                                    }
                                }
                                for house in range(4):
                                    solution["solution"]["rows"].append([
                                        str(house + 1),
                                        names[name_perm[house]],
                                        hobbies[hobby_perm[house]],
                                        animals[animal_perm[house]],
                                        books[book_perm[house]],
                                        birthdays[birthday_perm[house]],
                                        musics[music_perm[house]]
                                    ])
                                return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())