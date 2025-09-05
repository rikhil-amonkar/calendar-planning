import itertools
import json

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3]  # Left to right
    names = ["Eric", "Arnold", "Peter"]
    book_genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]

    solutions = []

    for name_perm in itertools.permutations(names):
        house_to_name = {house: name_perm[i] for i, house in enumerate(houses)}
        name_to_house = {v: k for k, v in house_to_name.items()}

        # Clue 1: Eric is directly left of Arnold.
        if not (name_to_house["Eric"] + 1 == name_to_house["Arnold"]):
            continue

        for book_perm in itertools.permutations(book_genres):
            house_to_book = {house: book_perm[i] for i, house in enumerate(houses)}
            book_to_house = {v: k for k, v in house_to_book.items()}

            # Clue 4: mystery is somewhere to the left of beach (needs vac later, but we can skip now)
            # We'll check this after vacations are assigned since it references beach (vacation).

            for vac_perm in itertools.permutations(vacations):
                house_to_vac = {house: vac_perm[i] for i, house in enumerate(houses)}
                vac_to_house = {v: k for k, v in house_to_vac.items()}

                # Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
                if not (name_to_house["Peter"] > vac_to_house["beach"]):
                    continue

                # Clue 3: Peter is the person who prefers city breaks.
                if not (name_to_house["Peter"] == vac_to_house["city"]):
                    continue

                # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
                if not (book_to_house["mystery"] < vac_to_house["beach"]):
                    continue

                # Clue 5: The person who loves science fiction books is the person who loves beach vacations.
                if not (book_to_house["science fiction"] == vac_to_house["beach"]):
                    continue

                # If all constraints satisfied, record solution
                solutions.append((house_to_name, house_to_book, house_to_vac))

    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    # Assuming unique solution; if multiple, take the first for output
    house_to_name, house_to_book, house_to_vac = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation"],
            "rows": [
                [str(h), house_to_name[h], house_to_book[h], house_to_vac[h]] for h in houses
            ],
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))