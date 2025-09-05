import itertools
import json

def main():
    houses = range(5)
    names_all = ["Alice", "Bob", "Arnold", "Eric", "Peter"]
    vacations_all = ["cruise", "city", "camping", "beach", "mountain"]
    children_all = ["Bella", "Samantha", "Fred", "Meredith", "Timothy"]
    nationalities_all = ["dane", "norwegian", "brit", "german", "swede"]

    solutions = []
    for names in itertools.permutations(names_all):
        # Clue 8: Eric is not in the fifth house (index 4)
        if names[4] == "Eric":
            continue
        
        for vacations in itertools.permutations(vacations_all):
            # Clue 6: House 1 (index 0) vacation is "cruise"
            if vacations[0] != "cruise":
                continue
            # Clue 11: Bob is the person who enjoys camping trips.
            try:
                index_bob = names.index("Bob")
            except ValueError:
                continue
            if vacations[index_bob] != "camping":
                continue
            # Clue 13: The person who enjoys camping trips is not in the fifth house.
            if vacations[4] == "camping":
                continue

            for children in itertools.permutations(children_all):
                # Clue 7: House 4 (index 3) child is "Meredith"
                if children[3] != "Meredith":
                    continue
                # Clue 4: House 2 (index 1) child is not "Bella"
                if children[1] == "Bella":
                    continue

                for nations in itertools.permutations(nationalities_all):
                    # Clue 12: The Dane is in the fifth house (index 4)
                    if nations[4] != "dane":
                        continue

                    # Clue 1: The Norwegian is Peter.
                    valid = True
                    for i in houses:
                        if nations[i] == "norwegian" and names[i] != "Peter":
                            valid = False
                            break
                        if names[i] == "Peter" and nations[i] != "norwegian":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 2: The Swedish person is the one whose child is named Bella.
                    valid = True
                    for i in houses:
                        if nations[i] == "swede" and children[i] != "Bella":
                            valid = False
                            break
                        if children[i] == "Bella" and nations[i] != "swede":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Clue 3: The person who loves beach vacations is directly left of the person whose child is named Samantha.
                    found_pair = False
                    for i in range(4):
                        if vacations[i] == "beach" and children[i+1] == "Samantha":
                            found_pair = True
                            break
                    if not found_pair:
                        continue

                    # Clue 9: The Swedish person is somewhere to the right of the Norwegian.
                    try:
                        index_norwegian = nations.index("norwegian")
                        index_swede = nations.index("swede")
                    except ValueError:
                        continue
                    if index_swede <= index_norwegian:
                        continue

                    # Clue 10: There is one house between the house with child Fred and the house with vacation city.
                    try:
                        index_fred = children.index("Fred")
                        index_city = vacations.index("city")
                    except ValueError:
                        continue
                    if abs(index_fred - index_city) != 2:
                        continue

                    # Clue 5: Alice is the British person.
                    valid = True
                    for i in houses:
                        if names[i] == "Alice" and nations[i] != "brit":
                            valid = False
                            break
                        if nations[i] == "brit" and names[i] != "Alice":
                            valid = False
                            break
                    if not valid:
                        continue

                    # All constraints satisfied; record the solution.
                    solution = []
                    for i in houses:
                        # House numbers are 1-indexed.
                        solution.append([str(i+1), names[i], vacations[i], children[i], nations[i]])
                    solutions.append(solution)

    if solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": solutions[0]
            }
        }
    else:
        output = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": []
            }
        }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()