import itertools
import json

def solve_puzzle():
    houses = [0, 1, 2]  # 0=House 1, 1=House 2, 2=House 3

    Names = ["Arnold", "Peter", "Eric"]
    Animals = ["bird", "horse", "cat"]
    Birthdays = ["jan", "sept", "april"]
    Hobbies = ["photography", "cooking", "gardening"]
    Drinks = ["milk", "water", "tea"]
    HairColors = ["black", "brown", "blonde"]

    solution = None

    for names in itertools.permutations(Names):
        # Clue 3: Eric is not in the first house.
        if names[0] == "Eric":
            continue

        idx_arnold = names.index("Arnold")

        for animals in itertools.permutations(Animals):
            # Clue 4: The cat lover is in the second house (index 1).
            if animals[1] != "cat":
                continue
            # Clue 8: Arnold is the bird keeper.
            if animals[idx_arnold] != "bird":
                continue

            for hair in itertools.permutations(HairColors):
                # Clue 7: The cat lover is the person who has brown hair. (cat at house 2 -> brown at house 2)
                if hair[1] != "brown":
                    continue

                for hobbies in itertools.permutations(Hobbies):
                    # Clue 1: The person who has brown hair is the person who loves cooking. (both at house 2)
                    if hobbies[1] != "cooking":
                        continue

                    # Additional enforcement of Clue 1 and 7 generally (not strictly needed due to pinning):
                    if animals[hair.index("brown")] != "cat":
                        continue
                    if hobbies[hair.index("brown")] != "cooking":
                        continue

                    for birthdays in itertools.permutations(Birthdays):
                        # Clue 2: The person whose birthday is in April is in the third house.
                        if birthdays[2] != "april":
                            continue
                        # Clue 10: September is directly left of Arnold.
                        if idx_arnold == 0:
                            continue
                        if birthdays[idx_arnold - 1] != "sept":
                            continue

                        for drinks in itertools.permutations(Drinks):
                            # Clue 6: The person who enjoys gardening is the person who likes milk.
                            if drinks[hobbies.index("gardening")] != "milk":
                                continue
                            # Clue 9: The one who only drinks water is the photography enthusiast.
                            if drinks[hobbies.index("photography")] != "water":
                                continue
                            # Clue 5: The person who has blonde hair is somewhere to the left of the person who likes milk.
                            if hair.index("blonde") >= drinks.index("milk"):
                                continue

                            # All constraints satisfied
                            solution = {
                                "Name": list(names),
                                "Animal": list(animals),
                                "Birthday": list(birthdays),
                                "Hobby": list(hobbies),
                                "Drink": list(drinks),
                                "HairColor": list(hair),
                            }
                            # Since solution is unique, break out
                            break
                        if solution:
                            break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    if not solution:
        raise RuntimeError("No solution found")

    # Build JSON output
    header = ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"]
    rows = []
    for i in houses:
        row = [
            str(i + 1),
            solution["Name"][i],
            solution["Animal"][i],
            solution["Birthday"][i],
            solution["Hobby"][i],
            solution["Drink"][i],
            solution["HairColor"][i],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()