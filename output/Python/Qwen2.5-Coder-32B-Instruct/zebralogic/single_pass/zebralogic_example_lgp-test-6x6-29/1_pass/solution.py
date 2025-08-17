import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    house_styles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
    cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(6)))

    # Check each permutation against the clues
    for name_order in permutations:
        for house_style_order in permutations:
            for food_order in permutations:
                for vacation_order in permutations:
                    for height_order in permutations:
                        for cigar_order in permutations:
                            # Unpack the orders into dictionaries for easier access
                            name_map = {i+1: names[name_order[i]] for i in range(6)}
                            house_style_map = {i+1: house_styles[house_style_order[i]] for i in range(6)}
                            food_map = {i+1: foods[food_order[i]] for i in range(6)}
                            vacation_map = {i+1: vacations[vacation_order[i]] for i in range(6)}
                            height_map = {i+1: heights[height_order[i]] for i in range(6)}
                            cigar_map = {i+1: cigars[cigar_order[i]] for i in range(6)}

                            # Check each clue
                            if (name_map[5] == "Alice" and
                                food_map[house_style_map.index("colonial")+1] == "stir fry" and
                                name_map[food_map.index("spaghetti")+1] == "Alice" and
                                name_map[food_map.index("stew")+1] == "Arnold" and
                                abs(height_map.index("average")+1 - name_map.index("Peter")+1) == 2 and
                                house_style_map[3] != "craftsman" and
                                height_map[food_map.index("stir fry")+1] == "average" and
                                house_style_map[vacation_map.index("beach")+1] == "ranch" and
                                name_map[4] == "Eric" and
                                abs(house_style_map.index("colonial")+1 - vacation_map.index("camping")+1) == 2 and
                                vacation_map[cigar_map.index("yellow monster")+1] == "mountain" and
                                height_map[vacation_map.index("mountain")+1] == "very tall" and
                                abs(cigar_map.index("dunhill")+1 - vacation_map.index("mountain")+1) == 1 and
                                house_style_map[food_map.index("spaghetti")+1] == "victorian" and
                                height_map[vacation_map.index("beach")+1] == "tall" and
                                name_map.index(vacation_map.index("beach")+1) < house_style_map.index("victorian")+1 and
                                food_map.index("stir fry")+1 == name_map.index("Bob")+1 and
                                house_style_map.index("modern")+1 < name_map.index("Alice")+1 and
                                house_style_map.index("craftsman")+1 < height_map.index("short")+1 and
                                food_map.index("stir fry")+1 < cigar_map.index("prince")+1 and
                                abs(food_map.index("grilled cheese")+1 - height_map.index("super tall")+1) == 3 and
                                cigar_map[house_style_map.index("ranch")+1] == "blue master" and
                                cigar_map.index("blends")+1 == cigar_map.index("blue master")+1 and
                                food_map[vacation_map.index("cultural")+1] == "pizza" and
                                food_map.index("pizza")+1 < vacation_map.index("cruise")+1):
                                
                                # If all clues are satisfied, construct the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
                                        "rows": []
                                    }
                                }
                                for house in range(1, 7):
                                    solution["solution"]["rows"].append([
                                        str(house),
                                        name_map[house],
                                        house_style_map[house],
                                        food_map[house],
                                        vacation_map[house],
                                        height_map[house],
                                        cigar_map[house]
                                    ])
                                return json.dumps(solution)

# Print the solution
print(solve_puzzle())