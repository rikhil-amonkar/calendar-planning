import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
    hobbies = ["cooking", "gardening", "painting", "photography", "knitting"]
    favorite_sports = ["swimming", "tennis", "soccer", "baseball", "basketball"]
    house_styles = ["ranch", "craftsman", "victorian", "modern", "colonial"]
    children = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
    heights = ["average", "very tall", "very short", "short", "tall"]

    # Generate all possible permutations
    for perm in itertools.permutations(zip(names, hobbies, favorite_sports, house_styles, children, heights)):
        # Unpack the permutation into individual lists
        name_order, hobby_order, sport_order, style_order, child_order, height_order = zip(*perm)

        # Check all constraints
        if (
            # 1. The person who has an average height is the person's child is named Meredith.
            height_order[child_order.index("Meredith")] == "average" and
            # 2. The person who is tall is in the second house.
            height_order[1] == "tall" and
            # 3. Peter is directly left of the person residing in a Victorian house.
            name_order.index("Peter") + 1 == style_order.index("victorian") and
            # 4. Alice is the person who is tall.
            name_order[height_order.index("tall")] == "Alice" and
            # 5. The person who loves baseball is the person who is very tall.
            sport_order[height_order.index("very tall")] == "baseball" and
            # 6. The person's child is named Meredith and the person who is the mother of Timothy are next to each other.
            abs(child_order.index("Meredith") - child_order.index("Timothy")) == 1 and
            # 7. Bob is the person who paints as a hobby.
            name_order[hobby_order.index("painting")] == "Bob" and
            # 8. The person who enjoys gardening is in the second house.
            hobby_order[1] == "gardening" and
            # 9. The person who is very short is somewhere to the right of Eric.
            height_order.index("very short") > names.index("Eric") and
            # 10. The person who loves tennis is the person's child is named Samantha.
            sport_order[child_order.index("Samantha")] == "tennis" and
            # 11. The person who loves soccer is not in the first house.
            sport_order[0] != "soccer" and
            # 12. The person's child is named Samantha is the person in a modern-style house.
            child_order[style_order.index("modern")] == "Samantha" and
            # 13. The person in a Craftsman-style house is the person who has an average height.
            style_order[height_order.index("average")] == "craftsman" and
            # 14. The person's child is named Fred is the person residing in a Victorian house.
            child_order[style_order.index("victorian")] == "Fred" and
            # 15. The person who is short is the person who loves basketball.
            height_order[sport_order.index("basketball")] == "short" and
            # 16. Peter is the person who is very tall.
            name_order[height_order.index("very tall")] == "Peter" and
            # 17. The person in a ranch-style home is somewhere to the left of the person who loves cooking.
            style_order.index("ranch") < sport_order.index("cooking") and
            # 18. The person who enjoys knitting and the person who enjoys gardening are next to each other.
            abs(hobby_order.index("knitting") - hobby_order.index("gardening")) == 1 and
            # 19. The person in a modern-style house is the person who loves cooking.
            style_order[sport_order.index("cooking")] == "modern" and
            # 20. The person residing in a Victorian house is in the fifth house.
            style_order[4] == "victorian"
        ):
            # If all constraints are satisfied, format the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
                    "rows": []
                }
            }
            for i in range(5):
                solution["solution"]["rows"].append([
                    str(i + 1),
                    name_order[i],
                    hobby_order[i],
                    sport_order[i],
                    style_order[i],
                    child_order[i],
                    height_order[i]
                ])
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())