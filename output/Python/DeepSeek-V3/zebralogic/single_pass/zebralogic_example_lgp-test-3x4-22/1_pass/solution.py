import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and their options
    houses = [1, 2, 3]
    names = ["Arnold", "Eric", "Peter"]
    music_genres = ["pop", "rock", "classical"]
    children = ["Fred", "Meredith", "Bella"]
    book_genres = ["mystery", "romance", "science fiction"]

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for music_perm in permutations(music_genres):
            for child_perm in permutations(children):
                for book_perm in permutations(book_genres):
                    # Assign each permutation to houses
                    solution = []
                    for i in range(3):
                        house = i + 1
                        name = name_perm[i]
                        music = music_perm[i]
                        child = child_perm[i]
                        book = book_perm[i]
                        solution.append({
                            "House": house,
                            "Name": name,
                            "MusicGenre": music,
                            "Children": child,
                            "BookGenre": book
                        })

                    # Check all constraints
                    valid = True

                    # Clue 2: Peter is in the first house
                    if solution[0]["Name"] != "Peter":
                        valid = False
                        continue

                    # Clue 5: Eric is the person who loves mystery books
                    eric_house = None
                    mystery_house = None
                    for house in solution:
                        if house["Name"] == "Eric":
                            eric_house = house
                        if house["BookGenre"] == "mystery":
                            mystery_house = house
                    if eric_house is None or mystery_house is None or eric_house["House"] != mystery_house["House"]:
                        valid = False
                        continue

                    # Clue 3: The person who loves mystery books loves classical music
                    if mystery_house["MusicGenre"] != "classical":
                        valid = False
                        continue

                    # Clue 1: The person whose child is Fred is directly left of the person who loves mystery books
                    fred_house = None
                    for house in solution:
                        if house["Children"] == "Fred":
                            fred_house = house
                    if fred_house is None or (fred_house["House"] + 1) != mystery_house["House"]:
                        valid = False
                        continue

                    # Clue 4: The person who loves science fiction books has child Meredith
                    sf_house = None
                    for house in solution:
                        if house["BookGenre"] == "science fiction":
                            sf_house = house
                    if sf_house is None or sf_house["Children"] != "Meredith":
                        valid = False
                        continue

                    # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books
                    rock_house = None
                    romance_house = None
                    for house in solution:
                        if house["MusicGenre"] == "rock":
                            rock_house = house
                        if house["BookGenre"] == "romance":
                            romance_house = house
                    if rock_house is None or romance_house is None or rock_house["House"] <= romance_house["House"]:
                        valid = False
                        continue

                    if valid:
                        # Prepare the output in the required format
                        output = {
                            "solution": {
                                "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                                "rows": []
                            }
                        }
                        for house in sorted(solution, key=lambda x: x["House"]):
                            output["solution"]["rows"].append([
                                str(house["House"]),
                                house["Name"],
                                house["MusicGenre"],
                                house["Children"],
                                house["BookGenre"]
                            ])
                        return json.dumps(output, indent=2)

    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())