import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Arnold", "Eric", "Alice"]
    flowers = ["daffodils", "carnations", "roses", "lilies"]
    heights = ["very short", "short", "tall", "average"]
    mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    occupations = ["engineer", "doctor", "teacher", "artist"]
    sports = ["swimming", "basketball", "tennis", "soccer"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(flowers)) + \
                       list(itertools.permutations(heights)) + \
                       list(itertools.permutations(mothers)) + \
                       list(itertools.permutations(occupations)) + \
                       list(itertools.permutations(sports))

    # Iterate over all possible combinations of permutations
    for names_perm, flowers_perm, heights_perm, mothers_perm, occupations_perm, sports_perm in itertools.product(all_permutations, repeat=6):
        # Unpack the permutations
        name_to_house = dict(zip(range(1, 5), names_perm))
        flower_to_house = dict(zip(range(1, 5), flowers_perm))
        height_to_house = dict(zip(range(1, 5), heights_perm))
        mother_to_house = dict(zip(range(1, 5), mothers_perm))
        occupation_to_house = dict(zip(range(1, 5), occupations_perm))
        sport_to_house = dict(zip(range(1, 5), sports_perm))

        # Check each clue
        if (sport_to_house[1] == "swimming" and flower_to_house[1] == "roses") or \
           (sport_to_house[2] == "swimming" and flower_to_house[2] == "roses") or \
           (sport_to_house[3] == "swimming" and flower_to_house[3] == "roses") or \
           (sport_to_house[4] == "swimming" and flower_to_house[4] == "roses"):
            continue

        if flower_to_house[1] != "roses" or names_perm[flower_to_house.index("roses")] != "Eric":
            continue

        if names_perm[heights_perm.index("tall")] != "Arnold":
            continue

        if flowers_perm.index("daffodils") <= occupations_perm.index("engineer"):
            continue

        if sport_to_house[1] != "soccer" or heights_perm[1] != "short" or \
           sport_to_house[2] != "soccer" or heights_perm[2] != "short" or \
           sport_to_house[3] != "soccer" or heights_perm[3] != "short" or \
           sport_to_house[4] != "soccer" or heights_perm[4] != "short":
            continue

        if names_perm[1] != "teacher":
            continue

        if mothers_perm[1] != "Janelle" or flowers_perm[1] != "carnations" or \
           mothers_perm[2] != "Janelle" or flowers_perm[2] != "carnations" or \
           mothers_perm[3] != "Janelle" or flowers_perm[3] != "carnations" or \
           mothers_perm[4] != "Janelle" or flowers_perm[4] != "carnations":
            continue

        if sport_to_house[1] != "basketball" or heights_perm[1] != "average" or \
           sport_to_house[2] != "basketball" or heights_perm[2] != "average" or \
           sport_to_house[3] != "basketball" or heights_perm[3] != "average" or \
           sport_to_house[4] != "basketball" or heights_perm[4] != "average":
            continue

        if names_perm[3] == "Arnold":
            continue

        if mothers_perm.index("Holly") <= heights_perm.index("average"):
            continue

        if names_perm[1] != "Peter" or occupations_perm[1] != "doctor" or \
           names_perm[2] != "Peter" or occupations_perm[2] != "doctor" or \
           names_perm[3] != "Peter" or occupations_perm[3] != "doctor" or \
           names_perm[4] != "Peter" or occupations_perm[4] != "doctor":
            continue

        if mothers_perm[1] != "Aniya" or names_perm[1] != "Alice" or \
           mothers_perm[2] != "Aniya" or names_perm[2] != "Alice" or \
           mothers_perm[3] != "Aniya" or names_perm[3] != "Alice" or \
           mothers_perm[4] != "Aniya" or names_perm[4] != "Alice":
            continue

        if names_perm[1] != "Arnold" or flowers_perm[1] != "lilies" or \
           names_perm[2] != "Arnold" or flowers_perm[2] != "lilies" or \
           names_perm[3] != "Arnold" or flowers_perm[3] != "lilies" or \
           names_perm[4] != "Arnold" or flowers_perm[4] != "lilies":
            continue

        # If all clues are satisfied, construct the solution
        solution = []
        for house in range(1, 5):
            solution.append([
                str(house),
                name_to_house[house],
                flower_to_house[house],
                height_to_house[house],
                mother_to_house[house],
                occupation_to_house[house],
                sport_to_house[house]
            ])

        # Output the solution in JSON format
        print(json.dumps({
            "solution": {
                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                "rows": solution
            }
        }, indent=2))
        return

solve_puzzle()