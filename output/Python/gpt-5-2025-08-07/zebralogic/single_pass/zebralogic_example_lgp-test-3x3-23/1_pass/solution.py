import json
from itertools import permutations

def solve_puzzle():
    # Input variables
    houses = [1, 2, 3]  # left to right
    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]

    solutions = []

    for name_perm in permutations(names):
        # Map house index -> name
        # house index 0 corresponds to house 1
        # Example: names_at_house[0] is the name at House 1
        names_at_house = list(name_perm)

        for occ_perm in permutations(occupations):
            occ_at_house = list(occ_perm)

            # Clue 5: The person who is an engineer is Peter.
            # Find the house of Peter and ensure occupation there is engineer
            try:
                house_of_peter = names_at_house.index("Peter")
            except ValueError:
                continue
            if occ_at_house[house_of_peter] != "engineer":
                continue

            for hobby_perm in permutations(hobbies):
                hobby_at_house = list(hobby_perm)

                # Helper functions to get positions (house indices 0..2)
                def pos_of_name(n): return names_at_house.index(n)
                def pos_of_occ(o): return occ_at_house.index(o)
                def pos_of_hobby(h): return hobby_at_house.index(h)

                # Clue 4: The photography enthusiast is the person who is a teacher.
                # So at the teacher's house, the hobby must be photography.
                teacher_pos = pos_of_occ("teacher")
                if hobby_at_house[teacher_pos] != "photography":
                    continue

                # Clue 2: The person who loves cooking is directly left of the person who is a teacher.
                if not (pos_of_hobby("cooking") + 1 == teacher_pos):
                    continue

                # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
                if not (pos_of_hobby("gardening") < pos_of_occ("doctor")):
                    continue

                # Clue 1: The person who is a doctor and Eric are next to each other.
                if abs(pos_of_occ("doctor") - pos_of_name("Eric")) != 1:
                    continue

                # All constraints satisfied; record solution
                solution_rows = []
                for i, house in enumerate(houses):
                    solution_rows.append([
                        str(house),
                        names_at_house[i],
                        occ_at_house[i],
                        hobby_at_house[i],
                    ])
                solutions.append(solution_rows)

    if not solutions:
        raise RuntimeError("No solution found.")
    # If multiple solutions, choose the first (should be unique for this puzzle)
    rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))