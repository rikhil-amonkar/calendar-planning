import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    heights = ["very short", "short", "tall", "average", "very tall"]
    mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
    hair_colors = ["blonde", "black", "gray", "red", "brown"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            for mother_perm in itertools.permutations(mothers):
                for hair_color_perm in itertools.permutations(hair_colors):
                    # Create a list of dictionaries for each house
                    houses_info = [
                        {"House": h, "Name": n, "Height": ht, "Mother": m, "HairColor": hc}
                        for h, n, ht, m, hc in zip(houses, name_perm, height_perm, mother_perm, hair_color_perm)
                    ]

                    # Check all clues
                    if (houses_info[heights.index("tall")]["Mother"] == "Holly" and
                        abs(houses_info[heights.index("average")]["House"] - houses_info[heights.index("short")]["House"]) == 2 and
                        houses_info[hair_colors.index("gray")]["House"] + 1 == houses_info[mothers.index("Janelle")]["House"] and
                        houses_info[hair_colors.index("black")]["House"] != 4 and
                        houses_info[names.index("Eric")]["HairColor"] == "black" and
                        houses_info[heights.index("very short")]["Mother"] == "Penny" and
                        abs(houses_info[names.index("Eric")]["House"] - houses_info[hair_colors.index("gray")]["House"]) == 1 and
                        houses_info[names.index("Bob")]["House"] == 5 and
                        houses_info[names.index("Peter")]["HairColor"] == "red" and
                        houses_info[mothers.index("Kailyn")]["House"] + 1 == houses_info[heights.index("short")]["House"] and
                        houses_info[names.index("Arnold")]["HairColor"] == "brown" and
                        houses_info[hair_colors.index("brown")]["House"] < houses_info[mothers.index("Janelle")]["House"] and
                        abs(houses_info[mothers.index("Aniya")]["House"] - houses_info[heights.index("very short")]["House"]) == 1 and
                        houses_info[mothers.index("Kailyn")]["House"] == 3):
                        
                        # If all conditions are satisfied, return the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                                "rows": [[str(h["House"]), h["Name"], h["Height"], h["Mother"], h["HairColor"]] for h in houses_info]
                            }
                        }
                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())