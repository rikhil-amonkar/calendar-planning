import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
    animals = ["horse", "dog", "bird", "fish", "cat"]
    nationalities = ["german", "swede", "norwegian", "brit", "dane"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(houses))

    for name_order in permutations:
        for smoothie_order in permutations:
            for animal_order in permutations:
                for nationality_order in permutations:
                    # Create a dictionary to store the solution
                    solution = {
                        house: {
                            "Name": name_order[house - 1],
                            "Smoothie": smoothie_order[house - 1],
                            "Animal": animal_order[house - 1],
                            "Nationality": nationality_order[house - 1]
                        }
                        for house in houses
                    }

                    # Check all the clues
                    if (nationality_order.index("swede") + 1 == animal_order.index("dog") and
                        abs(nationality_order.index("brit") - animal_order.index("dog")) == 2 and
                        nationality_order[2] == "dane" and
                        animal_order.index("bird") > animal_order.index("cat") and
                        animal_order.index("dog") + 1 == smoothie_order.index("lime") and
                        name_order.index("Eric") == animal_order.index("cat") and
                        name_order.index("Bob") == animal_order.index("bird") and
                        smoothie_order.index("cherry") + 1 == name_order.index("Peter") and
                        animal_order.index("bird") == smoothie_order.index("watermelon") and
                        smoothie_order.index("desert") == animal_order.index("dog") and
                        nationality_order[2] == "dane" and
                        nationality_order.index("norwegian") == name_order.index("Alice")):

                        # Prepare the output in the required format
                        output = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                                "rows": [
                                    [str(house), solution[house]["Name"], solution[house]["Smoothie"],
                                     solution[house]["Animal"], solution[house]["Nationality"]]
                                    for house in houses
                                ]
                            }
                        }

                        return json.dumps(output, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())