#!/usr/bin/env python3
import itertools
import json

def main():
    houses = [0, 1, 2]
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["tea", "water", "milk"]
    nationalities = ["dane", "brit", "swede"]
    educations = ["high school", "associate", "bachelor"]
    styles = ["victorian", "colonial", "ranch"]
    smoothies = ["cherry", "watermelon", "desert"]

    for p_names in itertools.permutations(names):
        for p_drinks in itertools.permutations(drinks):
            for p_nationalities in itertools.permutations(nationalities):
                for p_educations in itertools.permutations(educations):
                    # Clue 3: The person with a bachelor's degree is in the second house (index 1).
                    if p_educations[1] != "bachelor":
                        continue
                    for p_styles in itertools.permutations(styles):
                        # Clue 6: The person residing in a Victorian house is not in the first house.
                        if p_styles[0] == "victorian":
                            continue
                        for p_smoothies in itertools.permutations(smoothies):
                            valid = True
                            # Clue 2: The person who likes milk is the person in a ranch-style home.
                            for i in houses:
                                if p_drinks[i] == "milk" and p_styles[i] != "ranch":
                                    valid = False
                                    break
                                if p_styles[i] == "ranch" and p_drinks[i] != "milk":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 9: The person in a ranch-style home is the person with a high school diploma.
                            for i in houses:
                                if p_styles[i] == "ranch" and p_educations[i] != "high school":
                                    valid = False
                                    break
                                if p_educations[i] == "high school" and p_styles[i] != "ranch":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 4: The person with a high school diploma is the Dane.
                            for i in houses:
                                if p_educations[i] == "high school" and p_nationalities[i] != "dane":
                                    valid = False
                                    break
                                if p_nationalities[i] == "dane" and p_educations[i] != "high school":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 5: The Desert smoothie lover is the Swedish person.
                            for i in houses:
                                if p_smoothies[i] == "desert" and p_nationalities[i] != "swede":
                                    valid = False
                                    break
                                if p_nationalities[i] == "swede" and p_smoothies[i] != "desert":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 7: The person who likes Cherry smoothies is the person living in a colonial-style house.
                            for i in houses:
                                if p_smoothies[i] == "cherry" and p_styles[i] != "colonial":
                                    valid = False
                                    break
                                if p_styles[i] == "colonial" and p_smoothies[i] != "cherry":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 8: Arnold is somewhere to the right of the person residing in a Victorian house.
                            idx_victorian = None
                            idx_arnold = None
                            for i in houses:
                                if p_styles[i] == "victorian":
                                    idx_victorian = i
                                if p_names[i] == "Arnold":
                                    idx_arnold = i
                            if idx_victorian is None or idx_arnold is None or idx_arnold <= idx_victorian:
                                continue

                            # Clue 1: There is one house between Eric and the tea drinker.
                            idx_eric = None
                            idx_tea = None
                            for i in houses:
                                if p_names[i] == "Eric":
                                    idx_eric = i
                                if p_drinks[i] == "tea":
                                    idx_tea = i
                            if idx_eric is None or idx_tea is None or abs(idx_eric - idx_tea) != 2:
                                continue

                            # If all constraints are satisfied, build the solution.
                            solution_rows = []
                            for i in houses:
                                # House numbers are 1-indexed.
                                row = [
                                    str(i + 1),
                                    p_names[i],
                                    p_drinks[i],
                                    p_nationalities[i],
                                    p_educations[i],
                                    p_styles[i],
                                    p_smoothies[i]
                                ]
                                solution_rows.append(row)
                            header = ["House", "Name", "favorite drink", "nationality", "level of education", "style of house", "favorite smoothie"]
                            output = {"solution": {"header": header, "rows": solution_rows}}
                            print(json.dumps(output))
                            return

if __name__ == '__main__':
    main()