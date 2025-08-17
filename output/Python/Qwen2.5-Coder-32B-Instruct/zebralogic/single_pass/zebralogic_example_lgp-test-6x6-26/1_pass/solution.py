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

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for phone_perm in itertools.permutations(phones):
            for cigar_perm in itertools.permutations(cigars):
                for flower_perm in itertools.permutations(flowers):
                    for color_perm in itertools.permutations(colors):
                        for sport_perm in itertools.permutations(sports):
                            # Create a list of dictionaries for each house
                            houses_data = [
                                {"House": str(houses[i]), "Name": name_perm[i], "PhoneModel": phone_perm[i],
                                 "Cigar": cigar_perm[i], "Flower": flower_perm[i], "Color": color_perm[i],
                                 "FavoriteSport": sport_perm[i]}
                                for i in range(6)
                            ]

                            # Check all constraints
                            if (houses_data[1]["PhoneModel"] == "oneplus 9" and
                                houses_data.index({"PhoneModel": "xiaomi mi 11"}) < houses_data.index({"PhoneModel": "huawei p50"}) and
                                houses_data[flower_perm.index("carnations")]["Name"] == "Carol" and
                                houses_data[color_perm.index("purple")]["House"] == str(int(houses_data[cigar_perm.index("pall mall")]["House"]) - 1) and
                                houses_data[color_perm.index("green")]["Cigar"] == "blue master" and
                                abs(houses_data[color_perm.index("yellow")]["House"] - houses_data[color_perm.index("blue")]["House"]) == 1 and
                                houses_data.index({"Name": "Eric"}) > houses_data.index({"PhoneModel": "samsung galaxy s21"}) and
                                abs(houses_data[name_perm.index("Carol")]["House"] - houses_data[flower_perm.index("daffodils")]["House"]) == 2 and
                                houses_data[cigar_perm.index("prince")]["FavoriteSport"] == "basketball" and
                                houses_data[cigar_perm.index("dunhill")]["FavoriteSport"] == "volleyball" and
                                houses_data[phone_perm.index("google pixel 6")]["FavoriteSport"] == "swimming" and
                                houses_data[phone_perm.index("huawei p50")]["House"] == str(int(houses_data[color_perm.index("white")]["House"]) - 1) and
                                abs(houses_data[phone_perm.index("oneplus 9")]["House"] - houses_data[flower_perm.index("roses")]["House"]) == 1 and
                                houses_data[flower_perm.index("iris")]["House"] < houses_data[name_perm.index("Eric")]["House"] and
                                houses_data[cigar_perm.index("dunhill")]["Name"] == "Peter" and
                                houses_data[color_perm.index("blue")]["Name"] == "Peter" and
                                houses_data[name_perm.index("Bob")]["Flower"] == "tulips" and
                                houses_data[0]["Name"] == "Alice" and
                                houses_data[color_perm.index("yellow")]["House"] == str(int(houses_data[cigar_perm.index("blue master")]["House"]) - 1) and
                                houses_data[name_perm.index("Carol")]["FavoriteSport"] == "soccer" and
                                houses_data[flower_perm.index("carnations")]["House"] == str(int(houses_data[cigar_perm.index("blends")]["House"]) - 1) and
                                houses_data[name_perm.index("Eric")]["Cigar"] == "blends" and
                                houses_data[cigar_perm.index("volleyball")]["PhoneModel"] == "iphone 13" and
                                houses_data[phone_perm.index("google pixel 6")]["House"] > houses_data[cigar_perm.index("blends")]["House"]):
                                
                                # If all constraints are satisfied, return the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                                        "rows": [
                                            [str(house), name_perm[house-1], phone_perm[house-1], cigar_perm[house-1], flower_perm[house-1], color_perm[house-1], sport_perm[house-1]]
                                            for house in houses
                                        ]
                                    }
                                }
                                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())