import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals = ["dog", "horse", "cat", "bird", "fish"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for flower_perm in itertools.permutations(flowers):
            for animal_perm in itertools.permutations(animals):
                # Create a dictionary to map each house to its attributes
                house_map = {house: {"Name": name, "Flower": flower, "Animal": animal}
                             for house, name, flower, animal in zip(houses, name_perm, flower_perm, animal_perm)}

                # Check all constraints
                if (house_map[2]["Name"] == "Alice" and
                    house_map[next(h for h in houses if house_map[h]["Flower"] == "lilies")]["Animal"] == "bird" and
                    next(h for h in houses if house_map[h]["Name"] == "Peter") >
                    next(h for h in houses if house_map[h]["Flower"] == "tulips") and
                    house_map[next(h for h in houses if house_map[h]["Animal"] == "fish")]["Flower"] == "daffodils" and
                    house_map[next(h for h in houses if house_map[h]["Animal"] == "horse")]["Name"] == "Eric" and
                    abs(next(h for h in houses if house_map[h]["Animal"] == "dog") -
                        next(h for h in houses if house_map[h]["Name"] == "Bob")) == 2 and
                    next(h for h in houses if house_map[h]["Animal"] == "fish") + 1 ==
                    next(h for h in houses if house_map[h]["Name"] == "Bob") and
                    next(h for h in houses if house_map[h]["Name"] == "Alice") + 1 ==
                    next(h for h in houses if house_map[h]["Animal"] == "horse") and
                    next(h for h in houses if house_map[h]["Flower"] == "carnations") + 1 ==
                    next(h for h in houses if house_map[h]["Flower"] == "tulips") and
                    house_map[1]["Animal"] != "cat"):
                    # If all constraints are satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Flower", "Animal"],
                            "rows": [[str(house), house_map[house]["Name"], house_map[house]["Flower"], house_map[house]["Animal"]]
                                     for house in houses]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())