import itertools
import json

def solve_puzzle():
    # Houses indexed 0..2 correspond to house numbers 1..3 (left to right)
    houses = [0, 1, 2]

    # Attributes
    names = ['Arnold', 'Eric', 'Peter']
    music_genres = ['pop', 'rock', 'classical']
    children = ['Fred', 'Meredith', 'Bella']
    book_genres = ['mystery', 'romance', 'science fiction']

    solutions = []

    # Helper to invert a mapping value->position to position->value
    def invert_pos_map(pos_map, values):
        inv = {pos_map[val]: val for val in values}
        return [inv[i] for i in houses]

    for name_positions in itertools.permutations(houses):
        pos_name = {names[i]: name_positions[i] for i in range(3)}

        # Clue 2: Peter is in the first house (index 0)
        if pos_name['Peter'] != 0:
            continue

        # Now assign music permutations
        for music_positions in itertools.permutations(houses):
            pos_music = {music_genres[i]: music_positions[i] for i in range(3)}

            # Clue 3 and 5: Eric is the person who loves mystery books,
            # and the person who loves mystery books is also the one who loves classical music.
            # We'll enforce this later when assigning books, but we can already constrain music:
            # classical music must be at Eric's position.
            if pos_music['classical'] != pos_name['Eric']:
                continue

            # Assign children permutations
            for child_positions in itertools.permutations(houses):
                pos_child = {children[i]: child_positions[i] for i in range(3)}

                # Assign book permutations
                for book_positions in itertools.permutations(houses):
                    pos_book = {book_genres[i]: book_positions[i] for i in range(3)}

                    # Clue 5: Eric is the person who loves mystery books.
                    if pos_book['mystery'] != pos_name['Eric']:
                        continue

                    # Clue 3: The person who loves mystery books is the person who loves classical music.
                    if pos_book['mystery'] != pos_music['classical']:
                        continue

                    # Clue 1: The person whose child is Fred is directly left of the person who loves mystery books.
                    if pos_child['Fred'] + 1 != pos_book['mystery']:
                        continue

                    # Clue 4: The person who loves science fiction books is the person whose child is Meredith.
                    if pos_book['science fiction'] != pos_child['Meredith']:
                        continue

                    # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
                    if pos_music['rock'] <= pos_book['romance']:
                        continue

                    # All constraints satisfied; build solution rows by house order
                    name_by_pos = invert_pos_map(pos_name, names)
                    music_by_pos = invert_pos_map(pos_music, music_genres)
                    child_by_pos = invert_pos_map(pos_child, children)
                    book_by_pos = invert_pos_map(pos_book, book_genres)

                    rows = []
                    for i in houses:
                        rows.append([
                            str(i + 1),
                            name_by_pos[i],
                            music_by_pos[i],
                            child_by_pos[i],
                            book_by_pos[i]
                        ])
                    solutions.append(rows)

    # Expect a unique solution; if multiple, take the first for output consistency
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    rows = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))