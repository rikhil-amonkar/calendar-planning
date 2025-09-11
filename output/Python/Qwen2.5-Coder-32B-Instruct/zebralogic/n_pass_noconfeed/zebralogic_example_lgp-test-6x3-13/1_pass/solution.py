import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
    book_genres = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
    occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(range(6)))

    # Iterate over all permutations to find the correct solution
    for name_order in all_permutations:
        for book_genre_order in all_permutations:
            for occupation_order in all_permutations:
                # Create dictionaries to map positions to values
                name_map = {i + 1: names[name_order[i]] for i in range(6)}
                book_genre_map = {i + 1: book_genres[book_genre_order[i]] for i in range(6)}
                occupation_map = {i + 1: occupations[occupation_order[i]] for i in range(6)}

                # Check each clue
                if (name_map[book_genre_map.index("fantasy") + 1] == "Alice" and
                    abs(name_map.index("Bob") - book_genre_map.index("mystery")) == 1 and
                    name_map[book_genre_map.index("mystery") + 1] == "Carol" and
                    name_map[occupation_map.index("lawyer") + 1] == name_map[book_genre_map.index("fantasy") + 1] and
                    name_map.index("Bob") != 4 and
                    name_map.index("Arnold") < occupation_map.index("engineer") + 1 and
                    name_map.index("Alice") - occupation_map.index("nurse") - 1 == 1 and
                    name_map[occupation_map.index("teacher") + 1] == name_map[book_genre_map.index("biography") + 1] and
                    book_genre_map.index("historical fiction") < occupation_map.index("teacher") + 1 and
                    occupation_map[1] == "doctor" and
                    name_map[occupation_map.index("artist") + 1] == name_map[book_genre_map.index("science fiction") + 1] and
                    name_map[3] == "Eric" and
                    book_genre_map.index("mystery") != 4):
                    
                    # If all clues are satisfied, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "BookGenre", "Occupation"],
                            "rows": [
                                [str(i + 1), name_map[i + 1], book_genre_map[i + 1], occupation_map[i + 1]]
                                for i in range(6)
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Run the function and print the result
print(solve_puzzle())