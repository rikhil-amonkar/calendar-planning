import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    vacations = ["cruise", "city", "camping", "beach", "mountain"]
    children = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    nationalities = ["dane", "norwegian", "brit", "german", "swede"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(names))
    permutations_vacations = list(itertools.permutations(vacations))
    permutations_children = list(itertools.permutations(children))
    permutations_nationalities = list(itertools.permutations(nationalities))

    for perm_names in permutations:
        for perm_vacations in permutations_vacations:
            for perm_children in permutations_children:
                for perm_nationalities in permutations_nationalities:
                    # Unpack permutations for easier access
                    name_house = dict(zip(houses, perm_names))
                    vacation_house = dict(zip(houses, perm_vacations))
                    child_house = dict(zip(houses, perm_children))
                    nationality_house = dict(zip(houses, perm_nationalities))

                    # Check all clues
                    if (nationality_house[1] == "norwegian" and name_house[1] == "Peter" and
                        nationality_house[houses.index("swede")] > houses.index("norwegian") and
                        nationality_house[houses.index("swede")] != 2 and
                        child_house[houses.index("swede")] == "Bella" and
                        child_house[houses.index("bella")] != 2 and
                        name_house[houses.index("brit")] == "Alice" and
                        vacation_house[1] == "cruise" and
                        child_house[4] == "Meredith" and
                        name_house[5] != "Eric" and
                        nationality_house[5] == "dane" and
                        vacation_house[houses.index("camping")] != 5 and
                        name_house[houses.index("camping")] == "Bob" and
                        vacation_house[houses.index("beach")] + 1 == houses.index(child_house[houses.index("samantha")]) and
                        abs(houses.index(child_house[houses.index("fred")]) - houses.index(vacation_house[houses.index("city")])) == 2):
                        
                        # If all conditions are met, construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                                "rows": [
                                    [str(house), name_house[house], vacation_house[house], child_house[house], nationality_house[house]]
                                    for house in houses
                                ]
                            }
                        }

                        return json.dumps(solution, indent=2)

# Output the solution
print(solve_puzzle())