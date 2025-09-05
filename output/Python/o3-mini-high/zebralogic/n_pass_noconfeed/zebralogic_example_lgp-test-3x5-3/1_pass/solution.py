import itertools
import json

def main():
    # Define the possible attributes for the houses
    names = ["Eric", "Peter", "Arnold"]
    smoothies = ["cherry", "watermelon", "desert"]
    flowers = ["carnations", "lilies", "daffodils"]
    animals = ["cat", "horse", "bird"]
    hobbies = ["photography", "cooking", "gardening"]

    solutions = []

    # There are 3 houses, we assign each permutation to houses 0,1,2 representing houses 1,2,3.
    for perm_names in itertools.permutations(names):
        for perm_smoothies in itertools.permutations(smoothies):
            for perm_flowers in itertools.permutations(flowers):
                for perm_animals in itertools.permutations(animals):
                    for perm_hobbies in itertools.permutations(hobbies):
                        # Build the houses: index 0 = House 1, index 1 = House 2, index 2 = House 3.
                        houses = []
                        for i in range(3):
                            houses.append({
                                "Name": perm_names[i],
                                "Smoothie": perm_smoothies[i],
                                "Flower": perm_flowers[i],
                                "Animal": perm_animals[i],
                                "Hobby": perm_hobbies[i]
                            })
                        
                        valid = True

                        # Clue 8: The photography enthusiast is Eric.
                        for house in houses:
                            if house["Hobby"] == "photography" and house["Name"] != "Eric":
                                valid = False
                                break
                            if house["Name"] == "Eric" and house["Hobby"] != "photography":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 3: The person who loves cooking is the Desert smoothie lover.
                        for house in houses:
                            if house["Hobby"] == "cooking" and house["Smoothie"] != "desert":
                                valid = False
                                break
                            if house["Smoothie"] == "desert" and house["Hobby"] != "cooking":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 6: The person who loves a bouquet of daffodils is the Desert smoothie lover.
                        for house in houses:
                            if house["Flower"] == "daffodils" and house["Smoothie"] != "desert":
                                valid = False
                                break
                            if house["Smoothie"] == "desert" and house["Flower"] != "daffodils":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 2: The bird keeper is the person who likes Cherry smoothies.
                        for house in houses:
                            if house["Animal"] == "bird" and house["Smoothie"] != "cherry":
                                valid = False
                                break
                            if house["Smoothie"] == "cherry" and house["Animal"] != "bird":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 7: The Watermelon smoothie lover is the person who keeps horses.
                        for house in houses:
                            if house["Smoothie"] == "watermelon" and house["Animal"] != "horse":
                                valid = False
                                break
                            if house["Animal"] == "horse" and house["Smoothie"] != "watermelon":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue 5: The person who loves cooking is directly left of Peter.
                        # This means for some house i (with i < 2), house i has cooking and house i+1 is Peter.
                        found_pair = False
                        for i in range(2):
                            if houses[i]["Hobby"] == "cooking" and houses[i+1]["Name"] == "Peter":
                                found_pair = True
                                break
                        if not found_pair:
                            continue

                        # Clue 1: The person who keeps horses and the photography enthusiast (Eric) are next to each other.
                        index_horse = None
                        index_eric = None
                        for i, house in enumerate(houses):
                            if house["Animal"] == "horse":
                                index_horse = i
                            if house["Name"] == "Eric":
                                index_eric = i
                        if index_horse is None or index_eric is None or abs(index_horse - index_eric) != 1:
                            continue

                        # Clue 4: The person who enjoys gardening is the person who loves a carnations arrangement.
                        for house in houses:
                            if house["Hobby"] == "gardening" and house["Flower"] != "carnations":
                                valid = False
                                break
                            if house["Flower"] == "carnations" and house["Hobby"] != "gardening":
                                valid = False
                                break
                        if not valid:
                            continue

                        # If all constraints are satisfied, record the solution.
                        solutions.append(houses)
    
    # Assume exactly one valid solution exists.
    if solutions:
        solution = solutions[0]
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                "rows": []
            }
        }
        # Maintain order of houses 1, 2, 3.
        for i, house in enumerate(solution):
            row = [
                str(i + 1),
                house["Name"],
                house["Smoothie"],
                house["Flower"],
                house["Animal"],
                house["Hobby"]
            ]
            result["solution"]["rows"].append(row)
        
        print(json.dumps(result))

if __name__ == "__main__":
    main()