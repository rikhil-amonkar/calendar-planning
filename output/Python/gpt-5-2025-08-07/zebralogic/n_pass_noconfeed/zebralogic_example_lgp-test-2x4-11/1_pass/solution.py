import json
import itertools

def solve():
    # Houses are ordered left (1) to right (2)
    houses = [1, 2]

    # Attributes
    Names = ["Eric", "Arnold"]
    Hobbies = ["gardening", "photography"]
    Pets = ["cat", "dog"]
    Heights = ["short", "very short"]

    # Helper: generate mappings from value -> house
    def assignments(values):
        for perm in itertools.permutations(houses):
            yield dict(zip(values, perm))

    solutions = []

    for name_pos in assignments(Names):
        for height_pos in assignments(Heights):
            # Clue 2: Eric is the person who is very short.
            if name_pos["Eric"] != height_pos["very short"]:
                continue

            for hobby_pos in assignments(Hobbies):
                # Clue 1: The person who is very short is the photography enthusiast.
                if height_pos["very short"] != hobby_pos["photography"]:
                    continue

                for pet_pos in assignments(Pets):
                    # Clue 3: The person who has a cat is somewhere to the right of the person who is very short.
                    if not (pet_pos["cat"] > height_pos["very short"]):
                        continue

                    # Build house -> attributes mapping
                    house_to_name = {house: name for name, house in name_pos.items()}
                    house_to_hobby = {house: hobby for hobby, house in hobby_pos.items()}
                    house_to_pet = {house: pet for pet, house in pet_pos.items()}
                    house_to_height = {house: height for height, house in height_pos.items()}

                    solutions.append([
                        (str(h), house_to_name[h], house_to_hobby[h], house_to_pet[h], house_to_height[h])
                        for h in sorted(houses)
                    ])

    if not solutions:
        raise ValueError("No solution found.")

    # Assuming unique solution as typical with Zebra puzzles
    sol = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Pet", "Height"],
            "rows": [list(row) for row in sol]
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve()