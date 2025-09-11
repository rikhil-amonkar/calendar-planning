import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Arnold", "Eric"]
    occupations = ["doctor", "teacher", "engineer"]
    hobbies = ["cooking", "photography", "gardening"]

    # Define the constraints as functions
    def constraint1(houses):
        # The person who is a doctor and Eric are next to each other.
        doctor_index = houses[1].index("doctor")
        eric_index = houses[0].index("Eric")
        return abs(doctor_index - eric_index) == 1

    def constraint2(houses):
        # The person who loves cooking is directly left of the person who is a teacher.
        cooking_index = houses[2].index("cooking")
        teacher_index = houses[1].index("teacher")
        return cooking_index + 1 == teacher_index

    def constraint3(houses):
        # The person who is a doctor is somewhere to the right of the person who enjoys gardening.
        doctor_index = houses[1].index("doctor")
        gardening_index = houses[2].index("gardening")
        return doctor_index > gardening_index

    def constraint4(houses):
        # The photography enthusiast is the person who is a teacher.
        photography_index = houses[2].index("photography")
        teacher_index = houses[1].index("teacher")
        return photography_index == teacher_index

    def constraint5(houses):
        # The person who is an engineer is Peter.
        engineer_index = houses[1].index("engineer")
        peter_index = houses[0].index("Peter")
        return engineer_index == peter_index

    # Check each permutation against the constraints
    for name_perm in itertools.permutations(names):
        for occupation_perm in itertools.permutations(occupations):
            for hobby_perm in itertools.permutations(hobbies):
                houses = [name_perm, occupation_perm, hobby_perm]
                if (constraint1(houses) and
                    constraint2(houses) and
                    constraint3(houses) and
                    constraint4(houses) and
                    constraint5(houses)):
                    # If all constraints are satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Occupation", "Hobby"],
                            "rows": [
                                ["1", name_perm[0], occupation_perm[0], hobby_perm[0]],
                                ["2", name_perm[1], occupation_perm[1], hobby_perm[1]],
                                ["3", name_perm[2], occupation_perm[2], hobby_perm[2]]
                            ]
                        }
                    }
                    print(json.dumps(solution, indent=2))
                    return

# Run the solver
solve_puzzle()