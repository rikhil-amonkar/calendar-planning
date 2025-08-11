import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
    phones = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
    cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
    flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
    colors = ["yellow", "red", "green", "blue", "white", "purple"]
    sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

    # Initialize all possible assignments
    for name_assignment in permutations(names):
        # Clue 18: Alice is in the first house
        if name_assignment[0] != "Alice":
            continue

        for phone_assignment in permutations(phones):
            # Clue 1: oneplus 9 is in house 2
            if phone_assignment[1] != "oneplus 9":
                continue

            for cigar_assignment in permutations(cigars):
                # Clue 23: Eric smokes blends
                eric_index = name_assignment.index("Eric")
                if cigar_assignment[eric_index] != "blends":
                    continue

                for flower_assignment in permutations(flowers):
                    # Clue 3: Carol loves carnations
                    carol_index = name_assignment.index("Carol")
                    if flower_assignment[carol_index] != "carnations":
                        continue

                    # Clue 8: two houses between Carol and daffodils
                    try:
                        daffodils_index = flower_assignment.index("daffodils")
                        if abs(daffodils_index - carol_index) != 3:
                            continue
                    except ValueError:
                        continue

                    # Clue 22: carnations is directly left of blends
                    if carol_index + 1 != eric_index:
                        continue

                    for color_assignment in permutations(colors):
                        # Clue 4: purple is directly left of pall mall
                        try:
                            purple_index = color_assignment.index("purple")
                            pall_mall_index = cigar_assignment.index("pall mall")
                            if purple_index + 1 != pall_mall_index:
                                continue
                        except ValueError:
                            continue

                        # Clue 5: green color smokes blue master
                        try:
                            green_index = color_assignment.index("green")
                            if cigar_assignment[green_index] != "blue master":
                                continue
                        except ValueError:
                            continue

                        # Clue 6: yellow and blue are next to each other
                        try:
                            yellow_index = color_assignment.index("yellow")
                            blue_index = color_assignment.index("blue")
                            if abs(yellow_index - blue_index) != 1:
                                continue
                        except ValueError:
                            continue

                        # Clue 16: Peter loves blue
                        peter_index = name_assignment.index("Peter")
                        if color_assignment[peter_index] != "blue":
                            continue

                        # Clue 15: Peter smokes dunhill
                        if cigar_assignment[peter_index] != "dunhill":
                            continue

                        # Clue 10: dunhill smoker loves volleyball
                        for sport_assignment in permutations(sports):
                            if sport_assignment[peter_index] != "volleyball":
                                continue

                            # Clue 24: volleyball player uses iphone 13
                            if phone_assignment[peter_index] != "iphone 13":
                                continue

                            # Clue 11: swimming player uses google pixel 6
                            try:
                                swimming_index = sport_assignment.index("swimming")
                                if phone_assignment[swimming_index] != "google pixel 6":
                                    continue
                            except ValueError:
                                continue

                            # Clue 20: google pixel 6 is right of blends (eric)
                            try:
                                google_index = phone_assignment.index("google pixel 6")
                                if google_index <= eric_index:
                                    continue
                            except ValueError:
                                continue

                            # Clue 2: xiaomi mi 11 is left of huawei p50
                            try:
                                xiaomi_index = phone_assignment.index("xiaomi mi 11")
                                huawei_index = phone_assignment.index("huawei p50")
                                if xiaomi_index >= huawei_index:
                                    continue
                            except ValueError:
                                continue

                            # Clue 12: huawei p50 is directly left of white
                            try:
                                huawei_index = phone_assignment.index("huawei p50")
                                white_index = color_assignment.index("white")
                                if huawei_index + 1 != white_index:
                                    continue
                            except ValueError:
                                continue

                            # Clue 7: Eric is right of samsung galaxy s21
                            try:
                                samsung_index = phone_assignment.index("samsung galaxy s21")
                                if samsung_index >= eric_index:
                                    continue
                            except ValueError:
                                continue

                            # Clue 13: oneplus 9 (house 2) and roses are next to each other
                            try:
                                roses_index = flower_assignment.index("roses")
                                if abs(roses_index - 1) != 1:
                                    continue
                            except ValueError:
                                continue

                            # Clue 14: iris is left of Eric
                            try:
                                iris_index = flower_assignment.index("iris")
                                if iris_index >= eric_index:
                                    continue
                            except ValueError:
                                continue

                            # Clue 9: prince smoker loves basketball
                            try:
                                prince_index = cigar_assignment.index("prince")
                                if sport_assignment[prince_index] != "basketball":
                                    continue
                            except ValueError:
                                continue

                            # Clue 17: Bob loves tulips
                            try:
                                bob_index = name_assignment.index("Bob")
                                if flower_assignment[bob_index] != "tulips":
                                    continue
                            except ValueError:
                                continue

                            # Clue 19: baseball is directly left of blue master
                            try:
                                baseball_index = sport_assignment.index("baseball")
                                blue_master_index = cigar_assignment.index("blue master")
                                if baseball_index + 1 != blue_master_index:
                                    continue
                            except ValueError:
                                continue

                            # Clue 21: Carol loves soccer
                            if sport_assignment[carol_index] != "soccer":
                                continue

                            # All constraints satisfied, build solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Phone", "Cigar", "Flower", "Color", "Sport"],
                                    "rows": []
                                }
                            }
                            for i in range(6):
                                row = [
                                    str(i + 1),
                                    name_assignment[i],
                                    phone_assignment[i],
                                    cigar_assignment[i],
                                    flower_assignment[i],
                                    color_assignment[i],
                                    sport_assignment[i]
                                ]
                                solution["solution"]["rows"].append(row)
                            return solution

    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))