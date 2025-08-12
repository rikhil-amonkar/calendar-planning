import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    lunches = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(range(5)))

    # Iterate over all possible combinations of permutations
    for name_order in permutations:
        for hobby_order in permutations:
            for height_order in permutations:
                for lunch_order in permutations:
                    # Create dictionaries to map positions to values
                    name_map = {i + 1: names[name_order[i]] for i in range(5)}
                    hobby_map = {i + 1: hobbies[hobby_order[i]] for i in range(5)}
                    height_map = {i + 1: heights[height_order[i]] for i in range(5)}
                    lunch_map = {i + 1: lunches[lunch_order[i]] for i in range(5)}

                    # Check all the clues
                    if (
                        # Clue 1: Bob is the photography enthusiast.
                        name_map[hobby_map.index("photography") + 1] == "Bob" and
                        # Clue 2: The person who loves eating grilled cheese is the person who is tall.
                        lunch_map[height_map.index("tall") + 1] == "grilled cheese" and
                        # Clue 3: Peter is not in the second house.
                        name_map[2] != "Peter" and
                        # Clue 4: The person who is tall is directly left of the person who loves stir fry.
                        lunch_map[height_map.index("tall") + 2] == "stir fry" and
                        # Clue 5: The person who loves cooking is the person who has an average height.
                        lunch_map[height_map.index("average") + 1] == "cooking" and
                        # Clue 6: Alice is directly left of the person who is a pizza lover.
                        name_map[lunch_map.index("pizza") + 1] == "Alice" and
                        # Clue 7: The person who loves the spaghetti eater is not in the second house.
                        lunch_map[2] != "spaghetti" and
                        # Clue 8: Eric is not in the fifth house.
                        name_map[5] != "Eric" and
                        # Clue 9: The person who is short is Peter.
                        height_map[name_map.index("Peter") + 1] == "short" and
                        # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
                        abs(height_map.index("average") - hobby_map.index("gardening")) == 1 and
                        # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
                        hobby_map.index("painting") + 1 == lunch_map.index("grilled cheese") and
                        # Clue 12: The person who is very short is in the fifth house.
                        height_map[5] == "very short" and
                        # Clue 13: The person who is tall is in the third house.
                        height_map[3] == "tall" and
                        # Clue 14: Alice is somewhere to the right of the photography enthusiast.
                        name_map.index("Alice") > hobby_map.index("photography")
                    ):
                        # If all clues are satisfied, construct the solution
                        solution = []
                        for house in range(1, 6):
                            solution.append([
                                str(house),
                                name_map[house],
                                hobby_map[house],
                                height_map[house],
                                lunch_map[house]
                            ])

                        # Return the solution in the required format
                        return {
                            "solution": {
                                "header": ["House", "Name", "Hobby", "Height", "Lunch"],
                                "rows": solution
                            }
                        }

# Solve the puzzle and print the result as JSON
print(json.dumps(solve_puzzle(), indent=2))