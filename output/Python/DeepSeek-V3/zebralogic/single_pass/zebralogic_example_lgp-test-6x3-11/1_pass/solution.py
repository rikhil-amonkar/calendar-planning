import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']

    # Initialize solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "hair color", "height"],
            "rows": []
        }
    }

    # We'll use a backtracking approach to assign attributes
    from constraint import Problem, AllDifferentConstraint

    problem = Problem()

    # Variables for each house: name, hair_color, height
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"hair_{house}", hair_colors)
        problem.addVariable(f"height_{house}", heights)

    # All attributes must be unique
    problem.addConstraint(AllDifferentConstraint(), [f"name_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"hair_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"height_{house}" for house in houses])

    # Apply clues
    # Clue 2: Alice is in the fourth house.
    problem.addConstraint(lambda x: x == 'Alice', ["name_4"])

    # Clue 3: The person who is short is Arnold.
    for house in houses:
        problem.addConstraint(
            lambda name, height: not (name == 'Arnold' and height != 'short') and not (height == 'short' and name != 'Arnold'),
            [f"name_{house}", f"height_{house}"]
        )

    # Clue 4: The person who is tall is in the sixth house.
    problem.addConstraint(lambda x: x == 'tall', ["height_6"])

    # Clue 5: The person who has black hair is not in the fourth house.
    problem.addConstraint(lambda x: x != 'black', ["hair_4"])

    # Clue 6: The person who has red hair is Eric.
    for house in houses:
        problem.addConstraint(
            lambda name, hair: not (name == 'Eric' and hair != 'red') and not (hair == 'red' and name != 'Eric'),
            [f"name_{house}", f"hair_{house}"]
        )

    # Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
    def super_tall_right_of_average(*heights):
        avg_pos = None
        super_pos = None
        for i, height in enumerate(heights):
            if height == 'average':
                avg_pos = i + 1  # house numbers start at 1
            elif height == 'super tall':
                super_pos = i + 1
        if avg_pos is not None and super_pos is not None:
            return super_pos > avg_pos
        return True  # if one is missing, constraint is not violated

    problem.addConstraint(super_tall_right_of_average, [f"height_{house}" for house in houses])

    # Clue 8: The person who has blonde hair is Carol.
    for house in houses:
        problem.addConstraint(
            lambda name, hair: not (name == 'Carol' and hair != 'blonde') and not (hair == 'blonde' and name != 'Carol'),
            [f"name_{house}", f"hair_{house}"]
        )

    # Clue 9: There is one house between the person who has gray hair and the person who has red hair.
    def gray_red_spacing(*hairs):
        gray_pos = None
        red_pos = None
        for i, hair in enumerate(hairs):
            if hair == 'gray':
                gray_pos = i + 1
            elif hair == 'red':
                red_pos = i + 1
        if gray_pos is not None and red_pos is not None:
            return abs(gray_pos - red_pos) == 2
        return True  # if one is missing, constraint is not violated

    problem.addConstraint(gray_red_spacing, [f"hair_{house}" for house in houses])

    # Clue 10: The person who is very short is in the fifth house.
    problem.addConstraint(lambda x: x == 'very short', ["height_5"])

    # Clue 11: Bob is the person who has brown hair.
    for house in houses:
        problem.addConstraint(
            lambda name, hair: not (name == 'Bob' and hair != 'brown') and not (hair == 'brown' and name != 'Bob'),
            [f"name_{house}", f"hair_{house}"]
        )

    # Clue 12: The person who has gray hair is in the third house.
    problem.addConstraint(lambda x: x == 'gray', ["hair_3"])

    # Clue 13: The person who has blonde hair is the person who is very tall.
    for house in houses:
        problem.addConstraint(
            lambda hair, height: not (hair == 'blonde' and height != 'very tall') and not (height == 'very tall' and hair != 'blonde'),
            [f"hair_{house}", f"height_{house}"]
        )

    # Clue 1: The person who has blonde hair is directly left of Bob.
    # This means the house with blonde hair is immediately to the left of Bob's house.
    def blonde_left_of_bob(*names_hairs):
        for i in range(5):  # houses 1-5 can be left of someone
            if names_hairs[i*2 + 1] == 'blonde':  # hair of house i+1
                if names_hairs[(i+1)*2] == 'Bob':  # name of house i+2
                    return True
        return False  # if no such pair exists, constraint is violated

    # We need to combine name and hair for each house
    combined = []
    for house in houses:
        combined.append(f"name_{house}")
        combined.append(f"hair_{house}")
    problem.addConstraint(blonde_left_of_bob, combined)

    # Solve the problem
    solutions = problem.getSolutions()
    if not solutions:
        return {"solution": {"header": [], "rows": []}}

    # Take the first solution (assuming it's unique)
    sol = solutions[0]

    # Prepare the output
    rows = []
    for house in houses:
        row = [
            str(house),
            sol[f"name_{house}"],
            sol[f"hair_{house}"],
            sol[f"height_{house}"]
        ]
        rows.append(row)

    solution["solution"]["rows"] = rows
    return solution

# Execute and print the solution
print(json.dumps(solve_puzzle(), indent=2))