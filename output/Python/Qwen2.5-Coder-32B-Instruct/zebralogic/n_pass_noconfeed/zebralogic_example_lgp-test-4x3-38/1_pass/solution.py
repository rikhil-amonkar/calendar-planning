import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]
    houses = [1, 2, 3, 4]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names))
    permutations_mothers = list(itertools.permutations(mothers))
    permutations_flowers = list(itertools.permutations(flowers))

    # Iterate through all combinations of permutations
    for perm_names in permutations:
        for perm_mothers in permutations_mothers:
            for perm_flowers in permutations_flowers:
                # Create a list of dictionaries for each house
                houses_list = [
                    {"House": houses[0], "Name": perm_names[0], "Mother": perm_mothers[0], "Flower": perm_flowers[0]},
                    {"House": houses[1], "Name": perm_names[1], "Mother": perm_mothers[1], "Flower": perm_flowers[1]},
                    {"House": houses[2], "Name": perm_names[2], "Mother": perm_mothers[2], "Flower": perm_flowers[2]},
                    {"House": houses[3], "Name": perm_names[3], "Mother": perm_mothers[3], "Flower": perm_flowers[3]}
                ]

                # Check clue 1: Alice is The person whose mother's name is Kailyn.
                if not any(house["Name"] == "Alice" and house["Mother"] == "Kailyn" for house in houses_list):
                    continue

                # Check clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
                index_janelle = next((i for i, house in enumerate(houses_list) if house["Mother"] == "Janelle"), None)
                index_arnold = next((i for i, house in enumerate(houses_list) if house["Name"] == "Arnold"), None)
                if index_janelle is None or index_arnold is None or index_janelle <= index_arnold:
                    continue

                # Check clue 3: Peter is somewhere to the right of the person who loves a carnations arrangement.
                index_carnations = next((i for i, house in enumerate(houses_list) if house["Flower"] == "carnations"), None)
                index_peter = next((i for i, house in enumerate(houses_list) if house["Name"] == "Peter"), None)
                if index_carnations is None or index_peter is None or index_peter <= index_carnations:
                    continue

                # Check clue 4: Eric is the person who loves a bouquet of daffodils.
                if not any(house["Name"] == "Eric" and house["Flower"] == "daffodils" for house in houses_list):
                    continue

                # Check clue 5: Arnold is The person whose mother's name is Holly.
                if not any(house["Name"] == "Arnold" and house["Mother"] == "Holly" for house in houses_list):
                    continue

                # Check clue 6: The person who loves a carnations arrangement is somewhere to the right of The person whose mother's name is Holly.
                if index_carnations is None or index_holly is None or index_carnations <= index_holly:
                    continue

                # Check clue 7: The person who loves the bouquet of lilies is directly left of Alice.
                index_lilies = next((i for i, house in enumerate(houses_list) if house["Flower"] == "lilies"), None)
                index_alice = next((i for i, house in enumerate(houses_list) if house["Name"] == "Alice"), None)
                if index_lilies is None or index_alice is None or index_lilies != index_alice - 1:
                    continue

                # Check clue 8: Alice is in the third house.
                if not any(house["Name"] == "Alice" and house["House"] == 3 for house in houses_list):
                    continue

                # If all clues are satisfied, return the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Flower"],
                        "rows": [[str(house["House"]), house["Name"], house["Mother"], house["Flower"]] for house in houses_list]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())