import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    heights = ["very short", "short", "tall", "average", "very tall"]
    mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
    hairs = ["blonde", "black", "gray", "red", "brown"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for height_perm in itertools.permutations(heights):
            for mother_perm in itertools.permutations(mothers):
                for hair_perm in itertools.permutations(hairs):
                    # Apply constraints
                    if (height_perm[name_perm.index("tall")] == "tall" and mother_perm[name_perm.index("tall")] == "Holly" and
                        abs(height_perm.index("average") - height_perm.index("short")) == 2 and
                        hair_perm.index("gray") + 1 == mother_perm.index("Janelle") and
                        hair_perm[3] != "black" and
                        name_perm[hair_perm.index("black")] == "Eric" and
                        abs(name_perm.index("Eric") - hair_perm.index("gray")) == 1 and
                        name_perm[4] == "Bob" and
                        hair_perm[name_perm.index("Peter")] == "red" and
                        mother_perm.index("Kailyn") + 1 == height_perm.index("short") and
                        name_perm[hair_perm.index("brown")] == "Arnold" and
                        hair_perm.index("brown") < mother_perm.index("Janelle") and
                        abs(mother_perm.index("Aniya") - height_perm.index("very short")) == 1 and
                        mother_perm[2] == "Kailyn"):
                        
                        # Construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Mother", "Hair"],
                                "rows": []
                            }
                        }
                        for i in range(5):
                            solution["solution"]["rows"].append([
                                str(i+1),
                                name_perm[i],
                                height_perm[i],
                                mother_perm[i],
                                hair_perm[i]
                            ])
                        return json.dumps(solution, indent=2)

# Solve and print the puzzle
print(solve_puzzle())