import itertools
import json

def is_valid(assignment):
    # assignment is a list of tuples: (house, name, mother, flower)
    # Create a dictionary keyed by house number for easier constraint checking.
    houses = {house: {"name": name, "mother": mother, "flower": flower} for house, name, mother, flower in assignment}

    # Clue 8: Alice is in the third house.
    if houses[3]["name"] != "Alice":
        return False

    # Clue 1: Alice is the person whose mother's name is Kailyn.
    if houses[3]["mother"] != "Kailyn":
        return False

    # Clue 5: Arnold is the person whose mother's name is Holly.
    arnold_house = None
    for house in houses:
        if houses[house]["name"] == "Arnold":
            arnold_house = house
            if houses[house]["mother"] != "Holly":
                return False
            break
    if arnold_house is None:
        return False

    # Clue 4: Eric is the person who loves a bouquet of daffodils.
    eric_house = None
    for house in houses:
        if houses[house]["name"] == "Eric":
            eric_house = house
            if houses[house]["flower"] != "daffodils":
                return False
            break
    if eric_house is None:
        return False

    # Clue 7: The person who loves the bouquet of lilies is directly left of Alice.
    # Since Alice is in house 3 (Clue 8), house 2 must have the lilies.
    if 2 not in houses or houses[2]["flower"] != "lilies":
        return False

    # Clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
    janelle_house = None
    for house in houses:
        if houses[house]["mother"] == "Janelle":
            janelle_house = house
            break
    if janelle_house is None or janelle_house <= arnold_house:
        return False

    # Clue 6: The person who loves a carnations arrangement is somewhere to the right of the person whose mother's name is Holly.
    # Since Arnold's mother is Holly (Clue 5), the house with carnations must be to the right of Arnold's house.
    carnation_house = None
    for house in houses:
        if houses[house]["flower"] == "carnations":
            carnation_house = house
            break
    if carnation_house is None or carnation_house <= arnold_house:
        return False

    # Clue 3: Peter is somewhere to the right of the person who loves a carnations arrangement.
    peter_house = None
    for house in houses:
        if houses[house]["name"] == "Peter":
            peter_house = house
            break
    if peter_house is None or peter_house <= carnation_house:
        return False

    return True

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]

    for perm_names in itertools.permutations(names):
        for perm_mothers in itertools.permutations(mothers):
            for perm_flowers in itertools.permutations(flowers):
                assignment = list(zip(houses, perm_names, perm_mothers, perm_flowers))
                if is_valid(assignment):
                    return assignment
    return None

def main():
    solution = solve_puzzle()
    if solution is None:
        output = {"solution": {"header": ["House", "Name", "Mother", "Flower"], "rows": []}}
    else:
        # Sort the assignment by house number
        solution_sorted = sorted(solution, key=lambda x: x[0])
        rows = [[str(house), name, mother, flower] for house, name, mother, flower in solution_sorted]
        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "Flower"],
                "rows": rows
            }
        }
    print(json.dumps(output))

if __name__ == '__main__':
    main()