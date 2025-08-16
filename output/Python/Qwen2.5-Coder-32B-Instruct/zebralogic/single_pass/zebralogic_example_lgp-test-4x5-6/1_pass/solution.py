import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Eric", "Alice", "Arnold"]
    educations = ["bachelor", "high school", "associate", "master"]
    music_genres = ["jazz", "rock", "pop", "classical"]
    colors = ["green", "red", "yellow", "white"]
    flowers = ["lilies", "carnations", "daffodils", "roses"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(educations)) * \
                       list(itertools.permutations(music_genres)) * \
                       list(itertools.permutations(colors)) * \
                       list(itertools.permutations(flowers))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(names_perm, educations_perm, music_genres_perm, colors_perm, flowers_perm):
        # Unpack the permutations for easier access
        n1, n2, n3, n4 = names_perm
        e1, e2, e3, e4 = educations_perm
        m1, m2, m3, m4 = music_genres_perm
        c1, c2, c3, c4 = colors_perm
        f1, f2, f3, f4 = flowers_perm

        # Check each clue
        if e1 != "bachelor" or f1 != "daffodils":
            return False
        if f2 == "carnations" or f3 == "carnations" or f4 == "carnations":
            return False
        if e3 != "master" or n3 != "Alice":
            return False
        if e4 != "master" or m3 != "classical":
            return False
        if n2 == "Eric":
            return False
        if n3 == "Arnold":
            return False
        if c1 != "yellow" or f2 != "roses":
            return False
        if m2 != "pop":
            return False
        if e4 == "associate":
            return False
        if f4 == "carnations":
            return False
        if c1 != "red" or c2 != "white":
            return False
        if m1 != "rock":
            return False
        if n3 != "Arnold" or c3 != "yellow":
            return False
        if f1 != "daffodils" or c1 != "yellow":
            return False

        return True

    # Iterate over all possible combinations of permutations
    for names_perm in itertools.permutations(names):
        for educations_perm in itertools.permutations(educations):
            for music_genres_perm in itertools.permutations(music_genres):
                for colors_perm in itertools.permutations(colors):
                    for flowers_perm in itertools.permutations(flowers):
                        if is_valid_solution(names_perm, educations_perm, music_genres_perm, colors_perm, flowers_perm):
                            # If a valid solution is found, format it as JSON
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                                    "rows": [
                                        ["1", names_perm[0], educations_perm[0], music_genres_perm[0], colors_perm[0], flowers_perm[0]],
                                        ["2", names_perm[1], educations_perm[1], music_genres_perm[1], colors_perm[1], flowers_perm[1]],
                                        ["3", names_perm[2], educations_perm[2], music_genres_perm[2], colors_perm[2], flowers_perm[2]],
                                        ["4", names_perm[3], educations_perm[3], music_genres_perm[3], colors_perm[3], flowers_perm[3]]
                                    ]
                                }
                            }
                            print(json.dumps(solution))
                            return

# Run the function to solve the puzzle
solve_puzzle()