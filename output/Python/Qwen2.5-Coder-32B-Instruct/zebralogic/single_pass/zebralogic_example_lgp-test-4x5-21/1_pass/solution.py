import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Alice", "Peter", "Arnold"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports = ["soccer", "tennis", "basketball", "swimming"]
    cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers = ["daffodils", "roses", "lilies", "carnations"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(smoothies)) * \
                       list(itertools.permutations(sports)) * \
                       list(itertools.permutations(cars)) * \
                       list(itertools.permutations(flowers))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(permutation):
        name_order, smoothie_order, sport_order, car_order, flower_order = permutation

        # Unpack the permutation into separate lists
        name_to_house = {name: i for i, name in enumerate(name_order)}
        smoothie_to_house = {smoothie: i for i, smoothie in enumerate(smoothie_order)}
        sport_to_house = {sport: i for i, sport in enumerate(sport_order)}
        car_to_house = {car: i for i, car in enumerate(car_order)}
        flower_to_house = {flower: i for i, flower in enumerate(flower_order)}

        # Check each clue
        if car_to_house["tesla model 3"] != flower_to_house["roses"]:
            return False
        if name_to_house["Peter"] != smoothie_to_house["dragonfruit"]:
            return False
        if smoothie_to_house["desert"] != car_to_house["toyota camry"]:
            return False
        if sport_to_house["tennis"] != 0:
            return False
        if abs(car_to_house["toyota camry"] - sport_to_house["basketball"]) != 1:
            return False
        if name_to_house["Arnold"] != sport_to_house["basketball"]:
            return False
        if car_to_house["honda civic"] != flower_to_house["daffodils"]:
            return False
        if name_to_house["Eric"] != flower_to_house["roses"]:
            return False
        if smoothie_to_house["watermelon"] == 0:
            return False
        if car_to_house["honda civic"] <= smoothie_to_house["desert"]:
            return False
        if sport_to_house["basketball"] != flower_to_house["lilies"]:
            return False
        if abs(sport_to_house["tennis"] - sport_to_house["soccer"]) != 1:
            return False

        return True

    # Find the valid solution
    for permutation in all_permutations:
        if is_valid_solution(permutation):
            name_order, smoothie_order, sport_order, car_order, flower_order = permutation
            break

    # Prepare the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": [
                [str(i + 1), name_order[i], smoothie_order[i], sport_order[i], car_order[i], flower_order[i]]
                for i in range(4)
            ]
        }
    }

    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

# Run the solver
solve_puzzle()