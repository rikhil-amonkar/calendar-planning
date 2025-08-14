#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    houses_count = 5
    # Attributes as given in the puzzle
    names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals = ["dog", "horse", "cat", "bird", "fish"]
    
    # We'll iterate over all permutations of names, flowers, and animals.
    for perm_names in itertools.permutations(names):
        # Constraint 1: Alice is in the second house (house index 1).
        if perm_names[1] != "Alice":
            continue
        
        for perm_flowers in itertools.permutations(flowers):
            for perm_animals in itertools.permutations(animals):
                valid = True
                
                # Constraint 10: The cat lover is not in the first house (house index 0).
                if perm_animals[0] == "cat":
                    continue

                # Constraint 2: The person who loves the bouquet of lilies is the bird keeper.
                for i in range(houses_count):
                    if perm_flowers[i] == "lilies" and perm_animals[i] != "bird":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 4: The fish enthusiast is the person who loves a bouquet of daffodils.
                for i in range(houses_count):
                    if perm_flowers[i] == "daffodils" and perm_animals[i] != "fish":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 5: The person who keeps horses is Eric.
                # Find the house with the horse and make sure its owner is Eric.
                try:
                    horse_index = perm_animals.index("horse")
                except ValueError:
                    continue
                if perm_names[horse_index] != "Eric":
                    continue

                # Constraint 6: There are two houses between the dog owner and Bob.
                try:
                    dog_index = perm_animals.index("dog")
                    bob_index = perm_names.index("Bob")
                except ValueError:
                    continue
                if abs(dog_index - bob_index) != 3:
                    continue

                # Constraint 7: The fish enthusiast is directly left of Bob.
                try:
                    fish_index = perm_animals.index("fish")
                except ValueError:
                    continue
                if fish_index == houses_count - 1 or perm_names[fish_index + 1] != "Bob":
                    continue

                # Constraint 8: Alice is directly left of the person who keeps horses.
                try:
                    alice_index = perm_names.index("Alice")
                except ValueError:
                    continue
                # Check that Alice is not the rightmost house and the house immediately to her right has horse.
                if alice_index == houses_count - 1 or perm_animals[alice_index + 1] != "horse":
                    continue

                # Constraint 9: The person who loves a carnations arrangement is directly left of the person who loves the vase of tulips.
                try:
                    carnations_index = perm_flowers.index("carnations")
                except ValueError:
                    continue
                if carnations_index == houses_count - 1 or perm_flowers[carnations_index + 1] != "tulips":
                    continue

                # Constraint 3: Peter is somewhere to the right of the person who loves the vase of tulips.
                try:
                    tulips_index = perm_flowers.index("tulips")
                    peter_index = perm_names.index("Peter")
                except ValueError:
                    continue
                if peter_index <= tulips_index:
                    continue

                # If all constraints are satisfied, we have found the solution.
                solution = []
                for i in range(houses_count):
                    # House numbers as string, house ordering is from left (house 1) to right (house 5)
                    solution.append([
                        str(i + 1),
                        perm_names[i],
                        perm_flowers[i],
                        perm_animals[i]
                    ])
                return solution
    return None

def main():
    solution_rows = solve_puzzle()
    # Build the JSON output in the required structure.
    # The header must include all attribute names exactly as in the puzzle.
    output = {
        "solution": {
            "header": ["House", "Name", "favorite flower", "animal"],
            "rows": solution_rows if solution_rows is not None else []
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()