import itertools
import json

def main():
    houses_numbers = [1, 2]
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    favorite_sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]

    solutions = []

    for name_perm in itertools.permutations(names):
        for hair_perm in itertools.permutations(hair_colors):
            for sport_perm in itertools.permutations(favorite_sports):
                for smoothie_perm in itertools.permutations(smoothies):
                    houses = []
                    for i in range(len(houses_numbers)):
                        house_info = {
                            "House": str(houses_numbers[i]),
                            "Name": name_perm[i],
                            "HairColor": hair_perm[i],
                            "FavoriteSport": sport_perm[i],
                            "Smoothie": smoothie_perm[i]
                        }
                        houses.append(house_info)
                    
                    valid = True

                    # Clue 1: The Desert smoothie lover is Arnold.
                    for house in houses:
                        if house["Smoothie"] == "desert" and house["Name"] != "Arnold":
                            valid = False
                            break
                        if house["Name"] == "Arnold" and house["Smoothie"] != "desert":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 2: The person who has brown hair is the person who loves basketball.
                    for house in houses:
                        if house["HairColor"] == "brown" and house["FavoriteSport"] != "basketball":
                            valid = False
                            break
                        if house["FavoriteSport"] == "basketball" and house["HairColor"] != "brown":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 3: Arnold is somewhere to the left of the person who has black hair.
                    index_arnold = None
                    index_black = None
                    for idx, house in enumerate(houses):
                        if house["Name"] == "Arnold":
                            index_arnold = idx
                        if house["HairColor"] == "black":
                            index_black = idx
                    if index_arnold is None or index_black is None or index_arnold >= index_black:
                        continue

                    solutions.append(houses)
    
    if solutions:
        # Sort houses by their number to maintain the order from left to right.
        solution = sorted(solutions[0], key=lambda x: int(x["House"]))
        output = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                "rows": [
                    [house["House"], house["Name"], house["HairColor"], house["FavoriteSport"], house["Smoothie"]]
                    for house in solution
                ]
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()