import itertools
import json

def solve_puzzle():
    # Input variables (puzzle parameters)
    houses = [1, 2]  # Houses numbered from left (1) to right (2)
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]

    # Clues as input constraints
    # Eric is directly left of the person who loves mystery books
    clues = {
        "direct_left_of": [("Eric", "mystery")]  # (Name, BookGenre)
    }

    solutions = []

    # Brute-force search over all bijective assignments
    for name_positions in itertools.permutations(houses, len(names)):
        name_pos = dict(zip(names, name_positions))
        for genre_positions in itertools.permutations(houses, len(book_genres)):
            genre_pos = dict(zip(book_genres, genre_positions))

            # Apply constraints
            valid = True
            for (person_name, genre) in clues.get("direct_left_of", []):
                if name_pos[person_name] + 1 != genre_pos[genre]:
                    valid = False
                    break

            if not valid:
                continue

            # Build the solution table rows in house order
            header = ["House", "Name", "BookGenre"]
            rows = []
            for h in sorted(houses):
                # Find the name in house h
                house_name = next(n for n, p in name_pos.items() if p == h)
                # Find the genre in house h
                house_genre = next(g for g, p in genre_pos.items() if p == h)
                rows.append([str(h), house_name, house_genre])

            solutions.append({
                "solution": {
                    "header": header,
                    "rows": rows
                }
            })

    # Assuming a unique solution exists for the given puzzle
    if not solutions:
        # In case no solution found, still output the required structure with empty rows
        result = {
            "solution": {
                "header": ["House", "Name", "BookGenre"],
                "rows": [[str(h), "", ""] for h in sorted(houses)]
            }
        }
    else:
        result = solutions[0]

    print(json.dumps(result))

if __name__ == "__main__":
    solve_puzzle()