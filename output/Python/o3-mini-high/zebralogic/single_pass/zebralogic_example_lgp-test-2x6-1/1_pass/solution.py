#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the attributes as per the puzzle
    names = ["Arnold", "Eric"]
    sports = ["basketball", "soccer"]
    hair_colors = ["brown", "black"]
    heights = ["very short", "short"]
    smoothies = ["desert", "cherry"]
    flowers = ["daffodils", "carnations"]
    
    solution = None

    # There are 2 houses: index 0 corresponds to House 1, index 1 to House 2.
    for name_perm in itertools.permutations(names):
        for sports_perm in itertools.permutations(sports):
            for hair_perm in itertools.permutations(hair_colors):
                for height_perm in itertools.permutations(heights):
                    for smoothie_perm in itertools.permutations(smoothies):
                        for flower_perm in itertools.permutations(flowers):
                            # Build houses with assigned attributes
                            houses = []
                            for i in range(2):
                                house = {
                                    "House": str(i + 1),
                                    "Name": name_perm[i],
                                    "favorite sports": sports_perm[i],
                                    "hair colors": hair_perm[i],
                                    "heights": height_perm[i],
                                    "favorite smoothie": smoothie_perm[i],
                                    "favorite flower": flower_perm[i]
                                }
                                houses.append(house)
                            
                            # Clue 1: The person who loves soccer is not in the second house.
                            if houses[1]["favorite sports"] == "soccer":
                                continue
                            
                            # Clue 2: The Desert smoothie lover is directly left of the person who is very short.
                            # With 2 houses, this forces: House 1 must have "desert" and House 2 must be "very short".
                            if houses[0]["favorite smoothie"] != "desert" or houses[1]["heights"] != "very short":
                                continue
                            
                            # Clue 3: The person who is very short is the person who has brown hair.
                            valid = True
                            for house in houses:
                                if house["heights"] == "very short" and house["hair colors"] != "brown":
                                    valid = False
                                    break
                                if house["hair colors"] == "brown" and house["heights"] != "very short":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
                            valid = True
                            for house in houses:
                                if house["favorite smoothie"] == "desert" and house["favorite flower"] != "carnations":
                                    valid = False
                                    break
                                if house["favorite flower"] == "carnations" and house["favorite smoothie"] != "desert":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 5: Eric and the person who has brown hair are next to each other.
                            try:
                                index_eric = next(i for i, h in enumerate(houses) if h["Name"] == "Eric")
                                index_brown = next(i for i, h in enumerate(houses) if h["hair colors"] == "brown")
                            except StopIteration:
                                continue
                            if abs(index_eric - index_brown) != 1:
                                continue
                            
                            # All constraints satisfied: record solution.
                            solution = houses
                            break
                        if solution is not None:
                            break
                    if solution is not None:
                        break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    # Prepare the output in the specified JSON format.
    header = ["House", "Name", "favorite sports", "hair colors", "heights", "favorite smoothie", "favorite flower"]
    rows = []
    if solution is not None:
        # Ensure houses are ordered by their house number.
        solution = sorted(solution, key=lambda x: int(x["House"]))
        for house in solution:
            row = [house[key] for key in header]
            rows.append(row)

    output = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(output))

if __name__ == "__main__":
    main()