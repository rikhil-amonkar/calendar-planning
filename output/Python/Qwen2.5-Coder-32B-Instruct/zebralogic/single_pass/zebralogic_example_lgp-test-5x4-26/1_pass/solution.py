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
                    assignment = [
                        {"House": h, "Name": n, "Height": ht, "Mother": m, "HairColor": hc}
                        for h, n, ht, m, hc in zip(houses, name_perm, height_perm, mother_perm, hair_color_perm)
                    ]

                    # Check each clue
                    if (assignment[height_perm.index("tall")]["Mother"] == "Holly" and
                        abs(assignment[height_perm.index("average")]["House"] - assignment[height_perm.index("short")]["House"]) == 2 and
                        assignment[hair_color_perm.index("gray")]["House"] + 1 == assignment[mother_perm.index("Janelle")]["House"] and
                        assignment[hair_color_perm.index("black")]["House"] != 4 and
                        assignment[name_perm.index("Eric")]["HairColor"] == "black" and
                        assignment[height_perm.index("very short")]["Mother"] == "Penny" and
                        abs(assignment[name_perm.index("Eric")]["House"] - assignment[hair_color_perm.index("gray")]["House"]) == 1 and
                        assignment[name_perm.index("Bob")]["House"] == 5 and
                        assignment[name_perm.index("Peter")]["HairColor"] == "red" and
                        assignment[mother_perm.index("Kailyn")]["House"] + 1 == assignment[height_perm.index("short")]["House"] and
                        assignment[name_perm.index("Arnold")]["HairColor"] == "brown" and
                        assignment[hair_color_perm.index("brown")]["House"] < assignment[mother_perm.index("Janelle")]["House"] and
                        abs(assignment[mother_perm.index("Aniya")]["House"] - assignment[height_perm.index("very short")]["House"]) == 1 and
                        assignment[mother_perm.index("Kailyn")]["House"] == 3):
                        
                        # If all clues are satisfied, return the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                                "rows": [
                                    [str(a["House"]), a["Name"], a["Height"], a["Mother"], a["HairColor"]]
                                    for a in assignment
                                ]
                            }
                        }
                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())