import json
import itertools

def solve_puzzle():
    houses = [1, 2, 3]

    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    genres = ["science fiction", "romance", "mystery"]

    solutions = []

    # Iterate through all permutations for mapping each attribute to houses
    for name_pos in itertools.permutations(houses, len(names)):
        name_to_house = dict(zip(names, name_pos))

        # Clue 5: Peter is in the first house.
        if name_to_house["Peter"] != 1:
            continue

        for smoothie_pos in itertools.permutations(houses, len(smoothies)):
            smoothie_to_house = dict(zip(smoothies, smoothie_pos))

            for genre_pos in itertools.permutations(houses, len(genres)):
                genre_to_house = dict(zip(genres, genre_pos))

                # Apply constraints:

                # 1. Cherry smoothie is somewhere to the left of the person who loves mystery books.
                if not (smoothie_to_house["cherry"] < genre_to_house["mystery"]):
                    continue

                # 2. Arnold is the person who loves mystery books.
                if name_to_house["Arnold"] != genre_to_house["mystery"]:
                    continue

                # 3. Science fiction books is not in the first house.
                if genre_to_house["science fiction"] == 1:
                    continue

                # 4. The Desert smoothie lover is directly left of the person who loves mystery books.
                if smoothie_to_house["desert"] != genre_to_house["mystery"] - 1:
                    continue

                # All constraints satisfied; record solution
                solutions.append((name_to_house, smoothie_to_house, genre_to_house))

    # Use the first solution found (should be unique for a well-posed puzzle)
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    name_to_house, smoothie_to_house, genre_to_house = solutions[0]

    # Invert mappings to get attributes by house
    house_to_name = {h: n for n, h in name_to_house.items()}
    house_to_smoothie = {h: s for s, h in smoothie_to_house.items()}
    house_to_genre = {h: g for g, h in genre_to_house.items()}

    result = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": []
        }
    }

    for h in houses:
        row = [
            str(h),
            house_to_name[h],
            house_to_smoothie[h],
            house_to_genre[h],
        ]
        result["solution"]["rows"].append(row)

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))