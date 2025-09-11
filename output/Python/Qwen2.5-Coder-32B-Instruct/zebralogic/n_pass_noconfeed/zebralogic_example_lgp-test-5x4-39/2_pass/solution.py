import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    # Generate all possible combinations of permutations
    for names_perm, hobbies_perm, heights_perm, foods_perm in itertools.product(
            itertools.permutations(names),
            itertools.permutations(hobbies),
            itertools.permutations(heights),
            itertools.permutations(foods)
    ):
        # Unpack the permutations into lists for easier access
        names_list = list(names_perm)
        hobbies_list = list(hobbies_perm)
        heights_list = list(heights_perm)
        foods_list = list(foods_perm)

        # Check each clue
        if (
            # Clue 1: Bob is the photography enthusiast.
            names_list[hobbies_list.index("photography")] == "Bob" and
            # Clue 2: The person who loves eating grilled cheese is the person who is tall.
            heights_list[foods_list.index("grilled cheese")] == "tall" and
            # Clue 3: Peter is not in the second house.
            names_list[1] != "Peter" and
            # Clue 4: The person who is tall is directly left of the person who loves stir fry.
            heights_list.index("tall") + 1 == foods_list.index("stir fry") and
            # Clue 5: The person who loves cooking is the person who has an average height.
            heights_list[hobbies_list.index("cooking")] == "average" and
            # Clue 6: Alice is directly left of the person who is a pizza lover.
            names_list.index("Alice") + 1 == foods_list.index("pizza") and
            # Clue 7: The person who loves the spaghetti eater is not in the second house.
            foods_list[1] != "spaghetti" and
            # Clue 8: Eric is not in the fifth house.
            names_list[4] != "Eric" and
            # Clue 9: The person who is short is Peter.
            heights_list[names_list.index("Peter")] == "short" and
            # Clue 10: The person who has an average height and the person who enjoys gardening are next to each other.
            abs(heights_list.index("average") - hobbies_list.index("gardening")) == 1 and
            # Clue 11: The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
            hobbies_list.index("painting") + 1 == foods_list.index("grilled cheese") and
            # Clue 12: The person who is very short is in the fifth house.
            heights_list[4] == "very short" and
            # Clue 13: The person who is tall is in the third house.
            heights_list[2] == "tall" and
            # Clue 14: Alice is somewhere to the right of the photography enthusiast.
            names_list.index("Alice") > hobbies_list.index("photography")
        ):
            # If all clues are satisfied, construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Hobby", "Height", "Food"],
                    "rows": [
                        [str(i + 1), names_list[i], hobbies_list[i], heights_list[i], foods_list[i]]
                        for i in range(5)
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())