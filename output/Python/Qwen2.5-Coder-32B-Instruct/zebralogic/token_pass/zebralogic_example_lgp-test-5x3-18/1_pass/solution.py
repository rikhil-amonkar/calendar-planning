import itertools
import json

def solve_puzzle():
    # Define the possible values for each characteristic
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals = ["dog", "horse", "cat", "bird", "fish"]

    # Generate all possible permutations for each characteristic
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(flowers)) * \
                       list(itertools.permutations(animals))

    # Function to check if a permutation satisfies all clues
    def is_valid_solution(name_perm, flower_perm, animal_perm):
        # Unpack the permutations into dictionaries for easier access
        house_to_name = dict(zip(houses, name_perm))
        house_to_flower = dict(zip(houses, flower_perm))
        house_to_animal = dict(zip(houses, animal_perm))

        # Check each clue
        # Clue 1: Alice is in the second house.
        if house_to_name[2] != "Alice":
            return False

        # Clue 2: The person who loves the boquet of lilies is the bird keeper.
        if house_to_flower[house_to_animal.index("bird")] != "lilies":
            return False

        # Clue 3: Peter is somewhere to the right of the person who loves the vase of tulips.
        if house_to_name.index("Peter") <= house_to_flower.index("tulips"):
            return False

        # Clue 4: The fish enthusiast is the person who loves a bouquet of daffodils.
        if house_to_animal[house_to_flower.index("daffodils")] != "fish":
            return False

        # Clue 5: The person who keeps horses is Eric.
        if house_to_animal[house_to_name.index("Eric")] != "horse":
            return False

        # Clue 6: There are two houses between the dog owner and Bob.
        if abs(house_to_name.index("Bob") - house_to_animal.index("dog")) != 3:
            return False

        # Clue 7: The fish enthusiast is directly left of Bob.
        if house_to_name.index("Bob") - house_to_animal.index("fish") != 1:
            return False

        # Clue 8: Alice is directly left of the person who keeps horses.
        if house_to_name.index("Alice") + 1 != house_to_animal.index("horse"):
            return False

        # Clue 9: The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips.
        if house_to_flower.index("tulips") - house_to_flower.index("carnations") != 1:
            return False

        # Clue 10: The cat lover is not in the first house.
        if house_to_animal[1] == "cat":
            return False

        return True

    # Iterate over all possible permutations and find the valid solution
    for name_perm in itertools.permutations(names):
        for flower_perm in itertools.permutations(flowers):
            for animal_perm in itertools.permutations(animals):
                if is_valid_solution(name_perm, flower_perm, animal_perm):
                    # Format the solution as required
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Flower", "Animal"],
                            "rows": []
                        }
                    }
                    for house in houses:
                        solution["solution"]["rows"].append([
                            str(house),
                            house_to_name[house],
                            house_to_flower[house],
                            house_to_animal[house]
                        ])
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())