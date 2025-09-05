import json
import itertools

def solve_puzzle():
    houses_count = 2
    names = ["Arnold", "Eric"]
    sports = ["basketball", "soccer"]
    hair_colors = ["brown", "black"]
    heights = ["very short", "short"]
    smoothies = ["desert", "cherry"]
    flowers = ["daffodils", "carnations"]

    # Permutations for each attribute over the 2 houses (order corresponds to house positions 1,2)
    for name_perm in itertools.permutations(names):
        for sport_perm in itertools.permutations(sports):
            for hair_perm in itertools.permutations(hair_colors):
                for height_perm in itertools.permutations(heights):
                    for smoothie_perm in itertools.permutations(smoothies):
                        for flower_perm in itertools.permutations(flowers):
                            # Build houses as list of dicts, house index 0 is House "1", index 1 is House "2"
                            houses = []
                            for i in range(houses_count):
                                house = {
                                    "House": str(i+1),
                                    "Name": name_perm[i],
                                    "FavoriteSport": sport_perm[i],
                                    "HairColor": hair_perm[i],
                                    "Height": height_perm[i],
                                    "Smoothie": smoothie_perm[i],
                                    "Flower": flower_perm[i]
                                }
                                houses.append(house)

                            # Constraint 1: The person who loves soccer is not in the second house.
                            if houses[1]["FavoriteSport"] == "soccer":
                                continue

                            # Constraint 2: The Desert smoothie lover is directly left of the person who is very short.
                            # In 2 houses, the only possible scenario is that House1 has 'desert'
                            # and House2 must be the person who is 'very short'.
                            if houses[0]["Smoothie"] != "desert" or houses[1]["Smoothie"] == "desert":
                                continue
                            if houses[1]["Height"] != "very short":
                                continue

                            # Constraint 3: The person who is very short is the person who has brown hair.
                            valid_height_hair = True
                            for house in houses:
                                if house["Height"] == "very short" and house["HairColor"] != "brown":
                                    valid_height_hair = False
                                    break
                                if house["HairColor"] == "brown" and house["Height"] != "very short":
                                    valid_height_hair = False
                                    break
                            if not valid_height_hair:
                                continue

                            # Constraint 4: The person who loves a carnations arrangement is the Desert smoothie lover.
                            valid_flower_smoothie = True
                            for house in houses:
                                if (house["Smoothie"] == "desert" and house["Flower"] != "carnations") or \
                                   (house["Flower"] == "carnations" and house["Smoothie"] != "desert"):
                                    valid_flower_smoothie = False
                                    break
                            if not valid_flower_smoothie:
                                continue

                            # Constraint 5: Eric and the person who has brown hair are next to each other.
                            try:
                                eric_index = next(i for i, h in enumerate(houses) if h["Name"] == "Eric")
                                brown_index = next(i for i, h in enumerate(houses) if h["HairColor"] == "brown")
                            except StopIteration:
                                continue
                            if abs(eric_index - brown_index) != 1:
                                continue

                            # If we passed all constraints, we have found a solution.
                            return houses
    return None

def main():
    solution_houses = solve_puzzle()
    if solution_houses is None:
        output = {"solution": {"header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"], "rows": []}}
    else:
        # Sort houses by House number (which are strings but they represent numbers)
        solution_houses.sort(key=lambda h: int(h["House"]))
        header = ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"]
        rows = []
        for house in solution_houses:
            row = [house[attr] for attr in header]
            rows.append(row)
        output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()