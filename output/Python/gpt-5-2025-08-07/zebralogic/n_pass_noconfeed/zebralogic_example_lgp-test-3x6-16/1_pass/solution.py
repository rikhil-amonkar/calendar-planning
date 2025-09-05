import itertools
import json

def solve_puzzle():
    houses = [0, 1, 2]  # indices for houses 1..3

    Names = ["Eric", "Peter", "Arnold"]
    Drinks = ["tea", "water", "milk"]
    Nationalities = ["dane", "brit", "swede"]
    Educations = ["high school", "associate", "bachelor"]
    HouseStyles = ["victorian", "colonial", "ranch"]
    Smoothies = ["cherry", "watermelon", "desert"]

    solutions = []

    for names in itertools.permutations(Names):
        # Clue 8 depends on styles; defer
        for drinks in itertools.permutations(Drinks):
            # Clue 1: One house between Eric and the tea drinker (i.e., positions differ by 2)
            if abs(names.index("Eric") - drinks.index("tea")) != 2:
                continue

            for educ in itertools.permutations(Educations):
                # Clue 3: Bachelor's degree is in the second house (index 1)
                if educ.index("bachelor") != 1:
                    continue

                for nats in itertools.permutations(Nationalities):
                    # Clue 4: The person with a high school diploma is the Dane
                    if educ.index("high school") != nats.index("dane"):
                        continue

                    for styles in itertools.permutations(HouseStyles):
                        # Clue 6: Victorian house is not in the first house
                        if styles.index("victorian") == 0:
                            continue

                        # Clue 9: Ranch-style home is the person with a high school diploma
                        if styles.index("ranch") != educ.index("high school"):
                            continue

                        # Clue 2: Milk is the person in a ranch-style home
                        if drinks.index("milk") != styles.index("ranch"):
                            continue

                        # Clue 8: Arnold is somewhere to the right of the Victorian house
                        if names.index("Arnold") <= styles.index("victorian"):
                            continue

                        for smoothies in itertools.permutations(Smoothies):
                            # Clue 7: Cherry smoothies = Colonial house
                            if smoothies.index("cherry") != styles.index("colonial"):
                                continue

                            # Clue 5: Desert smoothie lover is the Swedish person
                            if smoothies.index("desert") != nats.index("swede"):
                                continue

                            # All constraints satisfied; construct solution
                            solution_rows = []
                            for i in houses:
                                row = [
                                    str(i + 1),
                                    names[i],
                                    drinks[i],
                                    nats[i],
                                    educ[i],
                                    styles[i],
                                    smoothies[i],
                                ]
                                solution_rows.append(row)

                            solutions.append(solution_rows)

    # Assume unique solution; take the first
    if not solutions:
        raise ValueError("No solution found.")
    result_rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
            "rows": result_rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()