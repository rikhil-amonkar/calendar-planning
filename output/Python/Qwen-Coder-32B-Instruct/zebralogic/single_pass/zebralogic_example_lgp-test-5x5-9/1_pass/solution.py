import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
    drinks = ["milk", "root beer", "coffee", "tea", "water"]
    colors = ["blue", "green", "white", "yellow", "red"]
    flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
    hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(range(5)))

    # Function to check if a given permutation satisfies all the clues
    def is_valid_solution(name_order, drink_order, color_order, flower_order, hobby_order):
        # Unpack the orders into lists
        name_list = [names[i] for i in name_order]
        drink_list = [drinks[i] for i in drink_order]
        color_list = [colors[i] for i in color_order]
        flower_list = [flowers[i] for i in flower_order]
        hobby_list = [hobbies[i] for i in hobby_order]

        # Check each clue
        if name_list[3] == "Alice":
            return False
        if drink_list[hobby_order.index("gardening")] != "root beer":
            return False
        if color_list[drink_order.index("coffee")] != "green":
            return False
        if flower_list[color_order.index("green")] != "lilies":
            return False
        if color_order.index("blue") <= flower_order.index("daffodils"):
            return False
        if hobby_order[color_order.index("blue")] != "cooking":
            return False
        if name_order[drink_order.index("tea")] != name_order[name_order.index("Eric") + 1]:
            return False
        if name_list[drink_order.index("water")] != "Peter":
            return False
        if hobby_order[name_order.index("Arnold")] != "photography":
            return False
        if flower_list[color_order.index("white")] != "roses":
            return False
        if abs(flower_order.index("carnations") - color_order.index("red")) != 2:
            return False
        if hobby_order.index("cooking") >= hobby_order.index("painting"):
            return False
        if drink_order.index("water") != 2:
            return False
        if drink_list[flower_order.index("carnations")] != "root beer":
            return False
        if color_order.index("white") != 1:
            return False

        return True

    # Iterate over all possible permutations to find the valid solution
    for name_order in all_permutations:
        for drink_order in all_permutations:
            for color_order in all_permutations:
                for flower_order in all_permutations:
                    for hobby_order in all_permutations:
                        if is_valid_solution(name_order, drink_order, color_order, flower_order, hobby_order):
                            # Construct the solution in the required format
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                                    "rows": []
                                }
                            }
                            for i in range(5):
                                solution["solution"]["rows"].append([
                                    str(i + 1),
                                    names[name_order[i]],
                                    drinks[drink_order[i]],
                                    colors[color_order[i]],
                                    flowers[flower_order[i]],
                                    hobbies[hobby_order[i]]
                                ])
                            return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())