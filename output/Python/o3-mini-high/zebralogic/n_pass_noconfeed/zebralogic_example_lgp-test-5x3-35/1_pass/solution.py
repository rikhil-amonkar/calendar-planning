import itertools
import json

def valid_assignment(names, mothers, heights):
    # Clue 1: Alice is the person whose mother's name is Aniya.
    for i in range(5):
        if names[i] == "Alice" and mothers[i] != "Aniya":
            return False
        if mothers[i] == "Aniya" and names[i] != "Alice":
            return False

    # Clue 10: Eric is the person whose mother's name is Kailyn.
    for i in range(5):
        if names[i] == "Eric" and mothers[i] != "Kailyn":
            return False
        if mothers[i] == "Kailyn" and names[i] != "Eric":
            return False

    # Clue 3: The person whose mother's name is Janelle is Bob.
    for i in range(5):
        if names[i] == "Bob" and mothers[i] != "Janelle":
            return False
        if mothers[i] == "Janelle" and names[i] != "Bob":
            return False

    # Clue 6: The person who is very tall is Arnold.
    for i in range(5):
        if names[i] == "Arnold" and heights[i] != "very tall":
            return False
        if heights[i] == "very tall" and names[i] != "Arnold":
            return False

    # Clue 11: The person who is very short is in the fifth house.
    if heights[4] != "very short":
        return False

    # Clue 4: Peter is not in the second house.
    if names[1] == "Peter":
        return False

    # Clue 8: Eric is not in the fifth house.
    if names[4] == "Eric":
        return False

    # Clue 2: The person with an average height is somewhere to the left of the person whose mother's name is Penny.
    try:
        avg_index = heights.index("average")
        penny_index = mothers.index("Penny")
    except ValueError:
        return False
    if avg_index >= penny_index:
        return False

    # Clue 7: Bob is directly left of the person who has an average height.
    try:
        avg_index = heights.index("average")
    except ValueError:
        return False
    if avg_index == 0 or names[avg_index - 1] != "Bob":
        return False

    # Clue 5: The person who is short is directly left of Arnold.
    try:
        arnold_index = names.index("Arnold")
    except ValueError:
        return False
    if arnold_index == 0 or heights[arnold_index - 1] != "short":
        return False

    # Clue 9: The person who is very tall (Arnold) is somewhere to the right of the person whose mother's name is Holly.
    try:
        holly_index = mothers.index("Holly")
    except ValueError:
        return False
    if holly_index >= arnold_index:
        return False

    return True

def main():
    names_list = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers_list = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights_list = ["average", "very short", "short", "very tall", "tall"]

    for names in itertools.permutations(names_list):
        # Clue 4: Peter is not in the second house.
        if names[1] == "Peter":
            continue
        # Clue 8: Eric is not in the fifth house.
        if names[4] == "Eric":
            continue

        for mothers in itertools.permutations(mothers_list):
            # Quick checks for Clues 1, 3, and 10.
            valid_flag = True
            for i in range(5):
                if (names[i] == "Alice" and mothers[i] != "Aniya") or (mothers[i] == "Aniya" and names[i] != "Alice"):
                    valid_flag = False
                    break
                if (names[i] == "Eric" and mothers[i] != "Kailyn") or (mothers[i] == "Kailyn" and names[i] != "Eric"):
                    valid_flag = False
                    break
                if (names[i] == "Bob" and mothers[i] != "Janelle") or (mothers[i] == "Janelle" and names[i] != "Bob"):
                    valid_flag = False
                    break
            if not valid_flag:
                continue

            for heights in itertools.permutations(heights_list):
                # Clue 11: The person who is very short is in the fifth house.
                if heights[4] != "very short":
                    continue

                # Clue 6: The person who is very tall is Arnold.
                try:
                    arnold_index = names.index("Arnold")
                except ValueError:
                    continue
                if heights[arnold_index] != "very tall":
                    continue

                # Clue 5: The person who is short is directly left of Arnold.
                if arnold_index == 0 or heights[arnold_index - 1] != "short":
                    continue

                # Clue 7: Bob is directly left of the person who has an average height.
                try:
                    avg_index = heights.index("average")
                except ValueError:
                    continue
                if avg_index == 0 or names[avg_index - 1] != "Bob":
                    continue

                # Clue 2: The person with an average height is somewhere to the left of the person whose mother's name is Penny.
                try:
                    penny_index = mothers.index("Penny")
                except ValueError:
                    continue
                if avg_index >= penny_index:
                    continue

                # Clue 9: The person who is very tall is somewhere to the right of the person whose mother's name is Holly.
                try:
                    holly_index = mothers.index("Holly")
                except ValueError:
                    continue
                if holly_index >= arnold_index:
                    continue

                if valid_assignment(names, mothers, heights):
                    solution = []
                    for i in range(5):
                        solution.append([str(i + 1), names[i], mothers[i], heights[i]])
                    result = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Height"],
                            "rows": solution
                        }
                    }
                    print(json.dumps(result, indent=2))
                    return

if __name__ == "__main__":
    main()