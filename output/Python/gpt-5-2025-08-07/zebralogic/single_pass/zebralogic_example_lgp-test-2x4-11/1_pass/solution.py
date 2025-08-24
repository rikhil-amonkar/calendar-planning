import itertools
import json

def solve_zebra_puzzle():
    # Input variables (puzzle parameters)
    houses = [1, 2]  # left to right
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    pets = ["cat", "dog"]
    heights = ["short", "very short"]

    # Helper to build position maps: value -> house index
    def build_pos_map(assignment):
        # assignment is a tuple where index aligns with house index-1
        return {value: i + 1 for i, value in enumerate(assignment)}

    solutions = []

    # Enumerate assignments ensuring uniqueness via permutations
    for name_assign in itertools.permutations(names, len(houses)):
        name_pos = build_pos_map(name_assign)

        for height_assign in itertools.permutations(heights, len(houses)):
            height_pos = build_pos_map(height_assign)

            # Clue 2: Eric is the person who is very short.
            if name_pos["Eric"] != height_pos["very short"]:
                continue

            for hobby_assign in itertools.permutations(hobbies, len(houses)):
                hobby_pos = build_pos_map(hobby_assign)

                # Clue 1: The person who is very short is the photography enthusiast.
                if height_pos["very short"] != hobby_pos["photography"]:
                    continue

                for pet_assign in itertools.permutations(pets, len(houses)):
                    pet_pos = build_pos_map(pet_assign)

                    # Clue 3: The person who has a cat is somewhere to the right of the very short person.
                    if not (pet_pos["cat"] > height_pos["very short"]):
                        continue

                    # If all constraints satisfied, record solution
                    solution_rows = []
                    for h in houses:
                        row = [
                            str(h),
                            name_assign[h - 1],
                            hobby_assign[h - 1],
                            pet_assign[h - 1],
                            height_assign[h - 1],
                        ]
                        solution_rows.append(row)
                    solutions.append(solution_rows)

    if not solutions:
        raise RuntimeError("No solution found.")
    if len(solutions) > 1:
        # In case multiple solutions exist, we can still return the first,
        # but raise awareness by selecting the first consistently.
        pass

    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Pet", "Height"],
            "rows": solutions[0]
        }
    }
    return result

if __name__ == "__main__":
    result = solve_zebra_puzzle()
    print(json.dumps(result, ensure_ascii=False))