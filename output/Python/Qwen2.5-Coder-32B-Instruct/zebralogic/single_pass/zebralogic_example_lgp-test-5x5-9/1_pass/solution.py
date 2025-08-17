import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    drinks = ["milk", "root beer", "coffee", "tea", "water"]
    colors = ["blue", "green", "white", "yellow", "red"]
    flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for drink_perm in itertools.permutations(drinks):
            for color_perm in itertools.permutations(colors):
                for flower_perm in itertools.permutations(flowers):
                    for hobby_perm in itertools.permutations(hobbies):
                        # Create a dictionary to store the current permutation
                        house_dict = {house: {"Name": name, "Drink": drink, "Color": color, "Flower": flower, "Hobby": hobby}
                                      for house, name, drink, color, flower, hobby in zip(houses, name_perm, drink_perm, color_perm, flower_perm, hobby_perm)}

                        # Check all constraints
                        if (house_dict[4]["Name"] != "Alice" and
                            house_dict[next(i for i, h in enumerate(house_dict) if h["Drink"] == "root beer")]["Hobby"] == "gardening" and
                            house_dict[next(i for i, h in enumerate(house_dict) if h["Color"] == "green")]["Drink"] == "coffee" and
                            house_dict[next(i for i, h in enumerate(house_dict) if h["Color"] == "green")]["Flower"] == "lilies" and
                            next(i for i, h in enumerate(house_dict) if h["Color"] == "blue") > next(i for i, h in enumerate(house_dict) if h["Flower"] == "daffodils") and
                            house_dict[next(i for i, h in enumerate(house_dict) if h["Hobby"] == "cooking")]["Color"] == "blue" and
                            house_dict[houses.index(next(i for i, h in enumerate(house_dict) if h["Name"] == "Eric")) + 1]["Drink"] == "tea" and
                            house_dict[3]["Drink"] == "water" and
                            house_dict[next(i for i, h in enumerate(house_dict) if h["Name"] == "Arnold")]["Hobby"] == "photography" and
                            house_dict[next(i for i, h in enumerate(house_dict) if h["Color"] == "white")]["Flower"] == "roses" and
                            abs(next(i for i, h in enumerate(house_dict) if h["Flower"] == "carnations") - next(i for i, h in enumerate(house_dict) if h["Color"] == "red")) == 2 and
                            next(i for i, h in enumerate(house_dict) if h["Hobby"] == "cooking") < next(i for i, h in enumerate(house_dict) if h["Hobby"] == "painting") and
                            house_dict[3]["Drink"] == "water" and
                            house_dict[next(i for i, h in enumerate(house_dict) if h["Drink"] == "root beer")]["Flower"] == "carnations" and
                            house_dict[2]["Color"] == "white"):
                            # If all constraints are satisfied, format the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                                    "rows": [[str(house), house_dict[house]["Name"], house_dict[house]["Drink"], house_dict[house]["Color"], house_dict[house]["Flower"], house_dict[house]["Hobby"]] for house in houses]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())