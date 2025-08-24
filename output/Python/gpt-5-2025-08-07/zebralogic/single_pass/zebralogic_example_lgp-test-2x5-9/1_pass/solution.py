import itertools
import json

def solve_puzzle():
    # Houses numbered left to right as seen from across the street
    houses = [1, 2]

    # Attributes and their possible values
    attributes = {
        "Name": ["Arnold", "Eric"],
        "BookGenre": ["science fiction", "mystery"],
        "Vacation": ["mountain", "beach"],
        "Animal": ["cat", "horse"],
        "MusicGenre": ["rock", "pop"],
    }

    # Helper to build a mapping from houses to values for a given permutation
    def map_to_houses(values):
        return {house: value for house, value in zip(houses, values)}

    solutions = []

    # Iterate through all permutations for each attribute (small search space)
    for names in itertools.permutations(attributes["Name"]):
        name_map = map_to_houses(names)

        for books in itertools.permutations(attributes["BookGenre"]):
            book_map = map_to_houses(books)

            # Apply early constraint: The person who loves mystery books is in the first house.
            # This prunes the search space early.
            if book_map[1] != "mystery":
                continue

            for vacations in itertools.permutations(attributes["Vacation"]):
                vacation_map = map_to_houses(vacations)

                for animals in itertools.permutations(attributes["Animal"]):
                    animal_map = map_to_houses(animals)

                    # Constraint: The cat lover is not in the second house.
                    if animal_map[2] == "cat":
                        continue

                    for music in itertools.permutations(attributes["MusicGenre"]):
                        music_map = map_to_houses(music)

                        # Helper to find the house index for a given category value
                        def house_of(category_map, value):
                            for h, v in category_map.items():
                                if v == value:
                                    return h
                            return None

                        # Apply all constraints
                        # 1. The person who loves beach vacations is Eric.
                        if house_of(vacation_map, "beach") != house_of(name_map, "Eric"):
                            continue

                        # 2. The person who loves pop music is the person who loves beach vacations.
                        if house_of(music_map, "pop") != house_of(vacation_map, "beach"):
                            continue

                        # 3. The person who loves rock music is the person who loves mystery books.
                        if house_of(music_map, "rock") != house_of(book_map, "mystery"):
                            continue

                        # 4. The cat lover is not in the second house. (already enforced)
                        # 5. The person who loves mystery books is in the first house. (already enforced)

                        solution_map = {
                            "Name": name_map,
                            "BookGenre": book_map,
                            "Vacation": vacation_map,
                            "Animal": animal_map,
                            "MusicGenre": music_map,
                        }
                        solutions.append(solution_map)

    if not solutions:
        raise ValueError("No solution found.")
    if len(solutions) > 1:
        # In case multiple solutions exist, we select the first to conform to output spec
        # but this puzzle should yield a unique solution.
        pass

    sol = solutions[0]
    header = ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"]
    rows = []
    for h in sorted(houses):
        rows.append([
            str(h),
            sol["Name"][h],
            sol["BookGenre"][h],
            sol["Vacation"][h],
            sol["Animal"][h],
            sol["MusicGenre"][h],
        ])

    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))