import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
    hair_colors = ["auburn", "blonde", "brown", "black", "red", "gray"]
    heights = ["very tall", "average", "very short", "tall", "super tall", "short"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(hair_colors)) * \
                       list(itertools.permutations(heights))

    # Define the constraints as functions
    def constraint1(permutation):
        names, hair_colors, _ = permutation
        return hair_colors.index("blonde") == names.index("Bob") - 1

    def constraint2(permutation):
        _, _, heights = permutation
        return heights[3] == "average"

    def constraint3(permutation):
        names, _, heights = permutation
        return names.index("Arnold") == heights.index("short")

    def constraint4(permutation):
        _, _, heights = permutation
        return heights[5] == "tall"

    def constraint5(permutation):
        _, hair_colors, _ = permutation
        return hair_colors[3] != "black"

    def constraint6(permutation):
        names, hair_colors, _ = permutation
        return names.index("Eric") == hair_colors.index("red")

    def constraint7(permutation):
        _, _, heights = permutation
        avg_index = heights.index("average")
        super_tall_index = heights.index("super tall")
        return super_tall_index > avg_index

    def constraint8(permutation):
        _, hair_colors, _ = permutation
        return hair_colors.index("blonde") == names.index("Carol")

    def constraint9(permutation):
        _, hair_colors, _ = permutation
        return abs(hair_colors.index("gray") - hair_colors.index("red")) == 2

    def constraint10(permutation):
        _, _, heights = permutation
        return heights[4] == "very short"

    def constraint11(permutation):
        names, hair_colors, _ = permutation
        return names.index("Bob") == hair_colors.index("brown")

    def constraint12(permutation):
        _, hair_colors, _ = permutation
        return hair_colors[2] == "gray"

    def constraint13(permutation):
        _, hair_colors, heights = permutation
        return hair_colors.index("blonde") == heights.index("very tall")

    # Check each permutation against all constraints
    for permutation in itertools.product(all_permutations, repeat=1):
        if (constraint1(permutation) and
            constraint2(permutation) and
            constraint3(permutation) and
            constraint4(permutation) and
            constraint5(permutation) and
            constraint6(permutation) and
            constraint7(permutation) and
            constraint8(permutation) and
            constraint9(permutation) and
            constraint10(permutation) and
            constraint11(permutation) and
            constraint12(permutation) and
            constraint13(permutation)):
            names, hair_colors, heights = permutation[0]
            solution = {
                "solution": {
                    "header": ["House", "Name", "Hair Color", "Height"],
                    "rows": [
                        [str(i + 1), names[i], hair_colors[i], heights[i]] for i in range(6)
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            return

solve_puzzle()