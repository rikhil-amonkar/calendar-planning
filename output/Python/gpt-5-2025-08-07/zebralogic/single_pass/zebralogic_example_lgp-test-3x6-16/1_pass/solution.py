import itertools
import json

def solve_puzzle():
    # Attributes
    houses = [0, 1, 2]  # indices for houses 1..3
    Names = ['Eric', 'Peter', 'Arnold']
    Drinks = ['tea', 'water', 'milk']
    Nationalities = ['dane', 'brit', 'swede']
    Education = ['high school', 'associate', 'bachelor']
    HouseStyles = ['victorian', 'colonial', 'ranch']
    Smoothies = ['cherry', 'watermelon', 'desert']

    # Try all permutations with pruning according to clues
    for hs_perm in itertools.permutations(HouseStyles):
        # Clue 6: Victorian is not in the first house.
        if hs_perm[0] == 'victorian':
            continue

        for name_perm in itertools.permutations(Names):
            # Clue 8: Arnold is somewhere to the right of the Victorian house.
            if name_perm.index('Arnold') <= hs_perm.index('victorian'):
                continue

            for edu_perm in itertools.permutations(Education):
                # Clue 3: Bachelor's degree is in the second house.
                if edu_perm[1] != 'bachelor':
                    continue

                # Clues 2 and 9 (combined with 4): ranch = high school
                if edu_perm[hs_perm.index('ranch')] != 'high school':
                    continue

                for drink_perm in itertools.permutations(Drinks):
                    # Clue 2: milk = ranch
                    if drink_perm[hs_perm.index('ranch')] != 'milk':
                        continue

                    # Clue 1: One house between Eric and the tea drinker.
                    if abs(name_perm.index('Eric') - drink_perm.index('tea')) != 2:
                        continue

                    for sm_perm in itertools.permutations(Smoothies):
                        # Clue 7: Cherry = colonial
                        if sm_perm[hs_perm.index('colonial')] != 'cherry':
                            continue

                        for nat_perm in itertools.permutations(Nationalities):
                            # Clue 4: High school = Dane
                            if nat_perm[edu_perm.index('high school')] != 'dane':
                                continue

                            # Clue 5: Desert = Swede
                            if nat_perm[sm_perm.index('desert')] != 'swede':
                                continue

                            # All constraints satisfied
                            solution_rows = []
                            for i in houses:
                                row = [
                                    str(i + 1),
                                    name_perm[i],
                                    drink_perm[i],
                                    nat_perm[i],
                                    edu_perm[i],
                                    hs_perm[i],
                                    sm_perm[i],
                                ]
                                solution_rows.append(row)

                            return {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                                    "rows": solution_rows
                                }
                            }

    raise ValueError("No solution found")

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))