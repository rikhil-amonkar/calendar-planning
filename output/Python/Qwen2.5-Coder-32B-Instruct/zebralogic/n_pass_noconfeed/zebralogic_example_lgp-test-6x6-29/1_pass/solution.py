import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    house_styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
    cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(6)))

    def is_valid(solution):
        # Unpack the solution
        name_order, house_style_order, food_order, vacation_order, height_order, cigar_order = solution

        # Check each clue
        if name_order[4] != names.index("Alice"):
            return False
        if house_style_order[food_order.index(foods.index("stir fry"))] != house_styles.index("colonial"):
            return False
        if food_order[name_order.index(names.index("Alice"))] != foods.index("spaghetti"):
            return False
        if food_order[name_order.index(names.index("Arnold"))] != foods.index("stew"):
            return False
        if abs(name_order[heights.index(heights.index("average"))] - name_order[names.index("Peter")]) != 1:
            return False
        if house_style_order[2] == house_styles.index("craftsman"):
            return False
        if height_order[food_order.index(foods.index("stir fry"))] != heights.index("average"):
            return False
        if house_style_order[vacation_order.index(vacations.index("beach"))] != house_styles.index("ranch"):
            return False
        if name_order[3] != names.index("Eric"):
            return False
        if abs(house_style_order.index(house_styles.index("colonial")) - vacation_order.index(vacations.index("camping"))) != 1:
            return False
        if vacation_order[cigar_order.index(cigars.index("yellow monster"))] != vacations.index("mountain"):
            return False
        if height_order[vacation_order.index(vacations.index("mountain"))] != heights.index("very tall"):
            return False
        if abs(cigar_order.index(cigars.index("dunhill")) - vacation_order.index(vacations.index("mountain"))) == 1:
            return False
        if house_style_order[food_order.index(foods.index("spaghetti"))] != house_styles.index("victorian"):
            return False
        if height_order[vacation_order.index(vacations.index("beach"))] != heights.index("tall"):
            return False
        if name_order[heights.index(heights.index("tall"))] < house_style_order.index(house_styles.index("victorian")):
            return False
        if food_order.index(foods.index("stir fry")) + 1 != name_order[names.index("Bob")]:
            return False
        if house_style_order.index(house_styles.index("modern")) < name_order[names.index("Alice")]:
            return False
        if house_style_order.index(house_styles.index("craftsman")) < height_order.index(heights.index("short")):
            return False
        if food_order.index(foods.index("stir fry")) < cigar_order.index(cigars.index("prince")):
            return False
        if abs(food_order.index(foods.index("grilled cheese")) - height_order.index(heights.index("super tall"))) == 2:
            return False
        if house_style_order[vacation_order.index(vacations.index("beach"))] != cigar_order.index(cigars.index("blue master")):
            return False
        if cigar_order.index(cigars.index("blends")) + 1 != cigar_order.index(cigars.index("blue master")):
            return False
        if food_order[vacation_order.index(vacations.index("cultural"))] != foods.index("pizza"):
            return False
        if food_order.index(foods.index("pizza")) < vacation_order.index(vacations.index("cruise")):
            return False

        return True

    # Iterate through all permutations to find the correct one
    for name_order in permutations:
        for house_style_order in permutations:
            for food_order in permutations:
                for vacation_order in permutations:
                    for height_order in permutations:
                        for cigar_order in permutations:
                            solution = (name_order, house_style_order, food_order, vacation_order, height_order, cigar_order)
                            if is_valid(solution):
                                # Construct the result
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                                        "rows": []
                                    }
                                }
                                for i in range(6):
                                    result["solution"]["rows"].append([
                                        str(i + 1),
                                        names[name_order[i]],
                                        house_styles[house_style_order[i]],
                                        foods[food_order[i]],
                                        vacations[vacation_order[i]],
                                        heights[height_order[i]],
                                        cigars[cigar_order[i]]
                                    ])
                                return json.dumps(result, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())