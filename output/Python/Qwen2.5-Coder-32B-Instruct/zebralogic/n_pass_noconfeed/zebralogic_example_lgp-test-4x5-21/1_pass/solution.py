import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Alice", "Peter", "Arnold"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports = ["soccer", "tennis", "basketball", "swimming"]
    cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers = ["daffodils", "roses", "lilies", "carnations"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(4)))

    # Function to check if a permutation satisfies all the clues
    def is_valid(permutation):
        name_order = [names[i] for i in permutation]
        smoothie_order = [smoothies[i] for i in permutation]
        sport_order = [sports[i] for i in permutation]
        car_order = [cars[i] for i in permutation]
        flower_order = [flowers[i] for i in permutation]

        # Check each clue
        if car_order.index("tesla model 3") != flower_order.index("roses"):
            return False
        if name_order.index("Peter") != smoothie_order.index("dragonfruit"):
            return False
        if smoothie_order.index("desert") != car_order.index("toyota camry"):
            return False
        if sport_order.index("tennis") != 0:
            return False
        if abs(car_order.index("toyota camry") - sport_order.index("basketball")) != 1:
            return False
        if name_order.index("Arnold") != sport_order.index("basketball"):
            return False
        if car_order.index("honda civic") != flower_order.index("daffodils"):
            return False
        if name_order.index("Eric") != flower_order.index("roses"):
            return False
        if smoothie_order.index("watermelon") == 0:
            return False
        if car_order.index("honda civic") < smoothie_order.index("desert"):
            return False
        if sport_order.index("basketball") != flower_order.index("lilies"):
            return False
        if abs(sport_order.index("tennis") - sport_order.index("soccer")) != 1:
            return False

        return True

    # Find the valid permutation
    for perm in permutations:
        if is_valid(perm):
            name_order = [names[i] for i in perm]
            smoothie_order = [smoothies[i] for i in perm]
            sport_order = [sports[i] for i in perm]
            car_order = [cars[i] for i in perm]
            flower_order = [flowers[i] for i in perm]

            # Prepare the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                    "rows": [
                        ["1", name_order[0], smoothie_order[0], sport_order[0], car_order[0], flower_order[0]],
                        ["2", name_order[1], smoothie_order[1], sport_order[1], car_order[1], flower_order[1]],
                        ["3", name_order[2], smoothie_order[2], sport_order[2], car_order[2], flower_order[2]],
                        ["4", name_order[3], smoothie_order[3], sport_order[3], car_order[3], flower_order[3]]
                    ]
                }
            }

            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()