import json
from itertools import permutations

def solve_puzzle():
    # Define houses and attribute domains
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]

    solutions = []

    # Enumerate all possible assignments (permutations ensure uniqueness across houses)
    for name_perm in permutations(names):
        for sport_perm in permutations(sports):
            for hobby_perm in permutations(hobbies):
                # Build assignments per house
                name = {houses[i]: name_perm[i] for i in range(len(houses))}
                sport = {houses[i]: sport_perm[i] for i in range(len(houses))}
                hobby = {houses[i]: hobby_perm[i] for i in range(len(houses))}

                # Clue 1: The person who enjoys gardening is Arnold (bi-conditional)
                if any((hobby[h] == "gardening") != (name[h] == "Arnold") for h in houses):
                    continue

                # Clue 2: The photography enthusiast is not in the first house
                if hobby[houses[0]] == "photography":
                    continue

                # Clue 3: The person who loves soccer is not in the first house
                if sport[houses[0]] == "soccer":
                    continue

                solutions.append((name, sport, hobby))

    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    # Assuming unique solution; take the first
    name, sport, hobby = solutions[0]

    # Build output JSON structure
    output = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": []
        }
    }

    for h in sorted(houses):
        row = [
            str(h),
            name[h],
            sport[h],
            hobby[h]
        ]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()