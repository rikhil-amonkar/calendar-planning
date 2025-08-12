import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
    birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
    lunches = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
    cars = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(6)))

    # Function to check if a permutation satisfies all the clues
    def is_valid(permutation):
        # Unpack the permutation into dictionaries for easier access
        house_names = {house + 1: names[permutation[i]] for i, house in enumerate(permutations[0])}
        house_birthdays = {house + 1: birthdays[permutation[i]] for i, house in enumerate(permutations[1])}
        house_lunches = {house + 1: lunches[permutation[i]] for i, house in enumerate(permutations[2])}
        house_heights = {house + 1: heights[permutation[i]] for i, house in enumerate(permutations[3])}
        house_cars = {house + 1: cars[permutation[i]] for i, house in enumerate(permutations[4])}

        # Check each clue
        if house_cars[permutation.index(names.index("Peter")) + 1] != "honda civic":
            return False
        if house_cars[5] != "ford f150":
            return False
        if house_lunches[permutation.index(names.index("Eric")) + 1] == "stir fry" or house_lunches[permutation.index(names.index("Eric")) + 1] < house_lunches[permutation.index(names.index("Eric")) + 1]:
            return False
        if house_birthdays[permutation.index(names.index("Carol")) + 1] == "may" or house_birthdays[permutation.index(names.index("Carol")) + 1] < house_birthdays[permutation.index(names.index("Carol")) + 1]:
            return False
        if house_heights[permutation.index(heights.index("very short")) + 1] > house_birthdays[permutation.index(birthdays.index("april")) + 1]:
            return False
        if house_cars[3] == "bmw 3 series":
            return False
        if abs(house_lunches.index("stir fry") - house_lunches.index("pizza")) != 2:
            return False
        if house_lunches[permutation.index(names.index("Eric")) + 1] != "soup" or house_lunches[permutation.index(names.index("Eric")) + 1] + 1 != house_lunches[permutation.index(names.index("Eric")) + 1]:
            return False
        if abs(house_birthdays.index("may") - house_lunches.index("spaghetti")) != 1:
            return False
        if house_names[permutation.index(names.index("Alice")) + 1] + 1 != house_cars.index("bmw 3 series"):
            return False
        if house_cars[permutation.index(cars.index("tesla model 3")) + 1] > house_heights[permutation.index(heights.index("tall")) + 1]:
            return False
        if house_cars[permutation.index(cars.index("toyota camry")) + 1] != "very tall":
            return False
        if house_names[permutation.index(names.index("Peter")) + 1] + 1 != house_lunches.index("pizza"):
            return False
        if house_lunches[3] == "stew":
            return False
        if abs(house_birthdays.index("sept") - house_heights.index("very short")) != 1:
            return False
        if abs(house_birthdays.index("mar") - house_heights.index("super tall")) != 1:
            return False
        if house_heights[permutation.index(heights.index("tall")) + 1] != "Bob":
            return False
        if house_birthdays[permutation.index(names.index("Carol")) + 1] == "may" or house_birthdays[permutation.index(names.index("Carol")) + 1] > house_birthdays[permutation.index(birthdays.index("may")) + 1]:
            return False
        if house_heights[4] != "very short":
            return False
        if house_birthdays[permutation.index(names.index("Carol")) + 1] != "mar":
            return False
        if house_cars[permutation.index(names.index("Carol")) + 1] != "tesla model 3":
            return False
        if house_birthdays[permutation.index(names.index("Eric")) + 1] != "jan":
            return False

        return True

    # Find the valid permutation
    for perm in itertools.product(permutations, repeat=5):
        if is_valid(perm):
            house_names = {house + 1: names[perm[0][i]] for i, house in enumerate(permutations[0])}
            house_birthdays = {house + 1: birthdays[perm[1][i]] for i, house in enumerate(permutations[1])}
            house_lunches = {house + 1: lunches[perm[2][i]] for i, house in enumerate(permutations[2])}
            house_heights = {house + 1: heights[perm[3][i]] for i, house in enumerate(permutations[3])}
            house_cars = {house + 1: cars[perm[4][i]] for i, house in enumerate(permutations[4])}

            solution = {
                "solution": {
                    "header": ["House", "Name", "Birthday", "Lunch", "Height", "Car"],
                    "rows": [
                        [str(house), house_names[house], house_birthdays[house], house_lunches[house], house_heights[house], house_cars[house]]
                        for house in range(1, 7)
                    ]
                }
            }

            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())