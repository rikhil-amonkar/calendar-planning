import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Alice", "Peter", "Arnold", "Eric"]
    mothers = ["Holly", "Kailyn", "Janelle", "Aniya"]
    flowers = ["carnations", "roses", "lilies", "daffodils"]

    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for flower_perm in itertools.permutations(flowers):
                # Create a dictionary to map house number to attributes
                house_dict = {house: {"Name": name, "Mother": mother, "Flower": flower}
                              for house, name, mother, flower in zip(houses, name_perm, mother_perm, flower_perm)}

                # Check all constraints
                if (house_dict[3]["Name"] == "Alice" and
                    house_dict[3]["Mother"] == "Kailyn" and
                    house_dict[name_perm.index("Arnold")]["Mother"] == "Holly" and
                    house_dict[name_perm.index("Eric")]["Flower"] == "daffodils" and
                    house_dict[name_perm.index("Alice")]["Flower"] == "lilies" and
                    house_dict[name_perm.index("Alice")]["Mother"] == "Kailyn" and
                    house_dict[mother_perm.index("Janelle")]["House"] > house_dict[name_perm.index("Arnold")]["House"] and
                    house_dict[name_perm.index("Peter")]["House"] > house_dict[flower_perm.index("carnations")]["House"] and
                    house_dict[mother_perm.index("Holly")]["House"] < house_dict[flower_perm.index("carnations")]["House"]):
                    # If all constraints are satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Flower"],
                            "rows": [[str(house), house_dict[house]["Name"], house_dict[house]["Mother"], house_dict[house]["Flower"]]
                                     for house in houses]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())