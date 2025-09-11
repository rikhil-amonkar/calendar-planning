import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
    phone_models = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
    cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
    flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
    colors = ["yellow", "red", "green", "blue", "white", "purple"]
    sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(names))
    all_permutations.extend(list(itertools.permutations(phone_models)))
    all_permutations.extend(list(itertools.permutations(cigars)))
    all_permutations.extend(list(itertools.permutations(flowers)))
    all_permutations.extend(list(itertools.permutations(colors)))
    all_permutations.extend(list(itertools.permutations(sports)))

    # Check each permutation against the clues
    for perm in itertools.product(all_permutations, repeat=6):
        name_order, phone_order, cigar_order, flower_order, color_order, sport_order = perm

        if (
            # Clue 1
            phone_order[1] == "oneplus 9" and
            # Clue 2
            phone_order.index("xiaomi mi 11") < phone_order.index("huawei p50") and
            # Clue 3
            flower_order[name_order.index("Carol")] == "carnations" and
            # Clue 4
            color_order.index("purple") + 1 == cigar_order.index("pall mall") and
            # Clue 5
            color_order[cigar_order.index("blue master")] == "green" and
            # Clue 6
            abs(color_order.index("yellow") - color_order.index("blue")) == 1 and
            # Clue 7
            name_order.index("Eric") > phone_order.index("samsung galaxy s21") and
            # Clue 8
            abs(name_order.index("Carol") - flower_order.index("daffodils")) == 2 and
            # Clue 9
            cigar_order[sport_order.index("basketball")] == "prince" and
            # Clue 10
            cigar_order[sport_order.index("volleyball")] == "dunhill" and
            # Clue 11
            sport_order[phone_order.index("google pixel 6")] == "swimming" and
            # Clue 12
            phone_order.index("huawei p50") + 1 == color_order.index("white") and
            # Clue 13
            abs(phone_order.index("oneplus 9") - flower_order.index("roses")) == 1 and
            # Clue 14
            flower_order.index("iris") < name_order.index("Eric") and
            # Clue 15
            cigar_order[name_order.index("Peter")] == "dunhill" and
            # Clue 16
            color_order[name_order.index("Peter")] == "blue" and
            # Clue 17
            flower_order[name_order.index("Bob")] == "tulips" and
            # Clue 18
            name_order[0] == "Alice" and
            # Clue 19
            sport_order[cigar_order.index("blue master")] - 1 == name_order.index("Peter") and
            # Clue 20
            phone_order.index("google pixel 6") > cigar_order.index("blends") and
            # Clue 21
            sport_order[name_order.index("Carol")] == "soccer" and
            # Clue 22
            flower_order.index("carnations") + 1 == cigar_order.index("blends") and
            # Clue 23
            cigar_order[name_order.index("Eric")] == "blends" and
            # Clue 24
            sport_order[phone_order.index("iphone 13")] == "volleyball"
        ):
            solution = {
                "solution": {
                    "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                    "rows": []
                }
            }
            for i in range(6):
                solution["solution"]["rows"].append([
                    str(i + 1),
                    name_order[i],
                    phone_order[i],
                    cigar_order[i],
                    flower_order[i],
                    color_order[i],
                    sport_order[i]
                ])
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())