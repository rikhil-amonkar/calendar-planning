import itertools
import json

def solve_puzzle():
    # Houses are indexed 0..4 representing houses 1..5 from left to right
    houses = [0, 1, 2, 3, 4]

    # Attributes
    names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals = ["dog", "horse", "cat", "bird", "fish"]

    # Helper to get house index of a value in a house->value tuple
    def house_of(value_list, value):
        return value_list.index(value)

    solution = None

    # Iterate over all possible assignments of names to houses (house -> name)
    for name_at_house in itertools.permutations(names):
        # 1. Alice is in the second house.
        if name_at_house[1] != "Alice":
            continue

        # Iterate over all possible assignments of animals to houses (house -> animal)
        for animal_at_house in itertools.permutations(animals):
            # 10. The cat lover is not in the first house.
            if animal_at_house[0] == "cat":
                continue

            # 5. The person who keeps horses is Eric.
            if name_at_house[house_of(animal_at_house, "horse")] != "Eric":
                continue

            # 8. Alice is directly left of the person who keeps horses.
            if house_of(name_at_house, "Alice") + 1 != house_of(animal_at_house, "horse"):
                continue

            # 6. There are two houses between the dog owner and Bob.
            if abs(house_of(animal_at_house, "dog") - house_of(name_at_house, "Bob")) != 3:
                continue

            # 7. The fish enthusiast is directly left of Bob.
            if house_of(animal_at_house, "fish") + 1 != house_of(name_at_house, "Bob"):
                continue

            # Iterate over all possible assignments of flowers to houses (house -> flower)
            for flower_at_house in itertools.permutations(flowers):
                # 2. Lilies lover is the bird keeper (same house).
                if house_of(flower_at_house, "lilies") != house_of(animal_at_house, "bird"):
                    continue

                # 4. Fish enthusiast loves daffodils (same house).
                if house_of(animal_at_house, "fish") != house_of(flower_at_house, "daffodils"):
                    continue

                # 9. Carnations is directly left of tulips.
                if house_of(flower_at_house, "carnations") + 1 != house_of(flower_at_house, "tulips"):
                    continue

                # 3. Peter is somewhere to the right of the person who loves tulips.
                if house_of(name_at_house, "Peter") <= house_of(flower_at_house, "tulips"):
                    continue

                # If all constraints satisfied, we found a solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Flower", "Animal"],
                        "rows": [
                            [str(h + 1), name_at_house[h], flower_at_house[h], animal_at_house[h]]
                            for h in houses
                        ],
                    }
                }
                return solution

    raise ValueError("No solution found")

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))