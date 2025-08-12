import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
    phones = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
    cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
    flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
    colors = ["yellow", "red", "green", "blue", "white", "purple"]
    sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

    for name_perm in itertools.permutations(names):
        for phone_perm in itertools.permutations(phones):
            for cigar_perm in itertools.permutations(cigars):
                for flower_perm in itertools.permutations(flowers):
                    for color_perm in itertools.permutations(colors):
                        for sport_perm in itertools.permutations(sports):
                            # Clue 1
                            if phone_perm[1] != "oneplus 9":
                                continue
                            # Clue 2
                            if phone_perm.index("xiaomi mi 11") >= phone_perm.index("huawei p50"):
                                continue
                            # Clue 3
                            if flower_perm[name_perm.index("Carol")] != "carnations":
                                continue
                            # Clue 4
                            if color_perm.index("purple") + 1 != cigar_perm.index("pall mall"):
                                continue
                            # Clue 5
                            if color_perm[cigar_perm.index("blue master")] != "green":
                                continue
                            # Clue 6
                            if abs(color_perm.index("yellow") - color_perm.index("blue")) != 1:
                                continue
                            # Clue 7
                            if name_perm.index("Eric") <= phone_perm.index("samsung galaxy s21"):
                                continue
                            # Clue 8
                            if abs(name_perm.index("Carol") - flower_perm.index("daffodils")) != 2:
                                continue
                            # Clue 9
                            if cigar_perm[sport_perm.index("basketball")] != "prince":
                                continue
                            # Clue 10
                            if cigar_perm[sport_perm.index("volleyball")] != "dunhill":
                                continue
                            # Clue 11
                            if sport_perm[phone_perm.index("google pixel 6")] != "swimming":
                                continue
                            # Clue 12
                            if phone_perm.index("huawei p50") + 1 != color_perm.index("white"):
                                continue
                            # Clue 13
                            if abs(phone_perm.index("oneplus 9") - flower_perm.index("roses")) != 1:
                                continue
                            # Clue 14
                            if flower_perm.index("iris") >= name_perm.index("Eric"):
                                continue
                            # Clue 15
                            if cigar_perm[name_perm.index("Peter")] != "dunhill":
                                continue
                            # Clue 16
                            if color_perm[name_perm.index("Peter")] != "blue":
                                continue
                            # Clue 17
                            if flower_perm[name_perm.index("Bob")] != "tulips":
                                continue
                            # Clue 18
                            if name_perm[0] != "Alice":
                                continue
                            # Clue 19
                            if cigar_perm.index("blue master") - 1 != sport_perm.index("baseball"):
                                continue
                            # Clue 20
                            if phone_perm.index("google pixel 6") <= cigar_perm.index("blends"):
                                continue
                            # Clue 21
                            if sport_perm[name_perm.index("Carol")] != "soccer":
                                continue
                            # Clue 22
                            if flower_perm.index("carnations") + 1 != cigar_perm.index("blends"):
                                continue
                            # Clue 23
                            if cigar_perm[name_perm.index("Eric")] != "blends":
                                continue
                            # Clue 24
                            if sport_perm[phone_perm.index("iphone 13")] != "volleyball":
                                continue

                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Phone Model", "Favorite Cigar", "Favorite Flower", "Favorite Color", "Favorite Sport"],
                                    "rows": []
                                }
                            }

                            for i in range(6):
                                solution["solution"]["rows"].append([
                                    str(houses[i]),
                                    name_perm[i],
                                    phone_perm[i],
                                    cigar_perm[i],
                                    flower_perm[i],
                                    color_perm[i],
                                    sport_perm[i]
                                ])

                            return json.dumps(solution, indent=2)

print(solve_puzzle())