import itertools
import json

def solve_puzzle():
    # Define possible attributes
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    birthdays = ["april", "sept"]
    animals = ["horse", "cat"]
    
    solution = None

    # Iterate over every permutation assignment of attributes
    for perm_names in itertools.permutations(names):
        # Constraint 1: Eric is in the first house.
        if perm_names[0] != "Eric":
            continue

        for perm_book in itertools.permutations(book_genres):
            # Constraint 3: The person who loves science fiction is in the second house.
            if perm_book[1] != "science fiction":
                continue

            for perm_birthday in itertools.permutations(birthdays):
                # Constraint 2: Eric's birthday (first house) is in September.
                if perm_birthday[0] != "sept":
                    continue

                for perm_animal in itertools.permutations(animals):
                    # Constraint 4: The person who keeps horses is the person whose birthday is in September.
                    # Since house 1 (Eric) has birthday 'sept', he must keep horses.
                    if perm_animal[0] != "horse":
                        continue

                    # At this point, all constraints are satisfied.
                    solution = [
                        {"House": "1", "Name": perm_names[0], "BookGenre": perm_book[0], "Birthday": perm_birthday[0], "Animal": perm_animal[0]},
                        {"House": "2", "Name": perm_names[1], "BookGenre": perm_book[1], "Birthday": perm_birthday[1], "Animal": perm_animal[1]}
                    ]
                    return solution
    return solution

def main():
    sol = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": [
                [house["House"], house["Name"], house["BookGenre"], house["Birthday"], house["Animal"]]
                for house in sol
            ]
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()