import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Bob", "Peter", "Alice", "Arnold", "Carol"]
    car_models = ["ford f150", "honda civic", "toyota camry", "tesla model 3", "chevrolet silverado", "bmw 3 series"]
    mothers = ["Sarah", "Penny", "Holly", "Aniya", "Kailyn", "Janelle"]
    hobbies = ["photography", "cooking", "knitting", "gardening", "woodworking", "painting"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(6)))

    # Function to check if a permutation satisfies all the clues
    def is_valid(permutation):
        # Unpack the permutation into individual lists
        name_order = [names[i] for i in permutation]
        car_model_order = [car_models[i] for i in permutation]
        mother_order = [mothers[i] for i in permutation]
        hobby_order = [hobbies[i] for i in permutation]

        # Check each clue
        if car_model_order[5] != "toyota camry":
            return False
        if hobby_order[name_order.index("Carol")] != "photography":
            return False
        if mother_order[car_model_order.index("chevrolet silverado")] != "Aniya":
            return False
        if car_model_order[1] == "chevrolet silverado":
            return False
        if mother_order[car_model_order.index("ford f150")] != "Sarah":
            return False
        if name_order[car_model_order.index("bmw 3 series")] != "Bob":
            return False
        if mother_order[5] != "Kailyn":
            return False
        if name_order.index("Eric") + 1 != hobby_order.index("knitting"):
            return False
        if abs(mother_order.index("Sarah") - car_model_order.index("toyota camry")) != 1:
            return False
        if mother_order.index("Penny") < hobby_order.index("knitting"):
            return False
        if mother_order.index("Aniya") < car_model_order.index("honda civic"):
            return False
        if name_order.index("Alice") < car_model_order.index("ford f150"):
            return False
        if hobby_order[name_order.index("Eric")] != "gardening":
            return False
        if hobby_order.index("woodworking") > hobby_order.index("knitting"):
            return False
        if abs(mother_order.index("Sarah") - hobby_order.index("cooking")) != 1:
            return False
        if car_model_order[name_order.index("Arnold")] != "honda civic":
            return False
        if mother_order.index("Holly") + 1 != hobby_order.index("knitting"):
            return False

        return True

    # Find the valid permutation
    for perm in all_permutations:
        if is_valid(perm):
            # Unpack the valid permutation into individual lists
            name_order = [names[i] for i in perm]
            car_model_order = [car_models[i] for i in perm]
            mother_order = [mothers[i] for i in perm]
            hobby_order = [hobbies[i] for i in perm]

            # Prepare the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                    "rows": [
                        [str(i + 1), name_order[i], car_model_order[i], mother_order[i], hobby_order[i]]
                        for i in range(6)
                    ]
                }
            }

            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()