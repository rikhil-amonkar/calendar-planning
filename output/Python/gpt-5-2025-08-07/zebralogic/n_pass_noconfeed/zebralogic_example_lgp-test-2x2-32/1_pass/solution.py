import itertools
import json

def solve_puzzle():
    # Define the entities
    houses = [1, 2]  # House numbers from left(1) to right(2)
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]

    # Helper to get house index by attribute value
    def house_of(value, mapping):
        for h, v in mapping.items():
            if v == value:
                return h
        return None

    solutions = []

    # Iterate over all permutations for each attribute
    for name_perm in itertools.permutations(names):
        name_by_house = {house: name_perm[i] for i, house in enumerate(houses)}

        for book_perm in itertools.permutations(book_genres):
            book_by_house = {house: book_perm[i] for i, house in enumerate(houses)}

            # Apply clues and constraints

            # Clue 1: Eric is directly left of the person who loves mystery books.
            eric_house = house_of("Eric", name_by_house)
            mystery_house = house_of("mystery", book_by_house)
            if eric_house is None or mystery_house is None:
                continue
            if eric_house + 1 != mystery_house:
                continue

            # All constraints satisfied, record solution
            solutions.append((name_by_house, book_by_house))

    # Assuming a unique solution per the puzzle
    if not solutions:
        raise ValueError("No solution found.")
    name_by_house, book_by_house = solutions[0]

    # Build the output structure
    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": [
                [str(h), name_by_house[h], book_by_house[h]] for h in houses
            ]
        }
    }

    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))