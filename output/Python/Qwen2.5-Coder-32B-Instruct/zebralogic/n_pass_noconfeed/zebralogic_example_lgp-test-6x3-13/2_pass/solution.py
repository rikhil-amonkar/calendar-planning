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

                # Reverse maps to find positions of specific values
                name_position_map = {v: k for k, v in name_map.items()}
                book_genre_position_map = {v: k for k, v in book_genre_map.items()}
                occupation_position_map = {v: k for k, v in occupation_map.items()}

                # Check each clue
                if (name_map[book_genre_position_map["fantasy"]] == "Alice" and
                    abs(name_position_map["Bob"] - book_genre_position_map["mystery"]) == 1 and
                    name_map[book_genre_position_map["mystery"]] == "Carol" and
                    name_map[occupation_position_map["lawyer"]] == name_map[book_genre_position_map["fantasy"]] and
                    name_position_map["Bob"] != 4 and
                    name_position_map["Arnold"] < occupation_position_map["engineer"] and
                    name_position_map["Alice"] - occupation_position_map["nurse"] == 2 and
                    name_map[occupation_position_map["teacher"]] == name_map[book_genre_position_map["biography"]] and
                    book_genre_position_map["historical fiction"] < occupation_position_map["teacher"] and
                    occupation_map[1] == "doctor" and
                    name_map[occupation_position_map["artist"]] == name_map[book_genre_position_map["science fiction"]] and
                    name_map[3] == "Eric" and
                    book_genre_position_map["mystery"] != 4):
                    
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