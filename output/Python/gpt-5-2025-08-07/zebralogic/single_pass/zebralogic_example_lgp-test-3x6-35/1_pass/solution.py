import json
import itertools

def solve_puzzle():
    # Houses are indexed 0..2 (representing houses 1..3 from left to right)

    # Attributes
    Names = ['Eric', 'Arnold', 'Peter']
    Vacations = ['mountain', 'city', 'beach']
    Heights = ['very short', 'average', 'short']
    Flowers = ['carnations', 'daffodils', 'lilies']
    HairColors = ['brown', 'black', 'blonde']
    Educations = ['associate', 'bachelor', 'high school']

    # Indices for quick reference
    i_Eric = Names.index('Eric')
    i_Arnold = Names.index('Arnold')
    i_Peter = Names.index('Peter')

    i_mountain = Vacations.index('mountain')
    i_city = Vacations.index('city')
    i_beach = Vacations.index('beach')

    i_very_short = Heights.index('very short')
    i_average = Heights.index('average')
    i_short = Heights.index('short')

    i_carnations = Flowers.index('carnations')
    i_daffodils = Flowers.index('daffodils')
    i_lilies = Flowers.index('lilies')

    i_brown = HairColors.index('brown')
    i_black = HairColors.index('black')
    i_blonde = HairColors.index('blonde')

    i_associate = Educations.index('associate')
    i_bachelor = Educations.index('bachelor')
    i_high_school = Educations.index('high school')

    houses = [0, 1, 2]
    perms = list(itertools.permutations(houses))

    def invert_mapping(values_list, positions_perm):
        # positions_perm[val_index] = house_index
        inv = [''] * len(positions_perm)
        for idx, house in enumerate(positions_perm):
            inv[house] = values_list[idx]
        return inv

    solutions = []

    for p_name in perms:
        # No direct constraints on names alone

        for p_height in perms:
            # 1. Peter is the person who has an average height.
            if p_name[i_Peter] != p_height[i_average]:
                continue

            # 3. The person who is very short is not in the second house.
            if p_height[i_very_short] == 1:
                continue

            # 6. The person who is short is somewhere to the right of the person who is very short.
            if not (p_height[i_short] > p_height[i_very_short]):
                continue

            for p_vac in perms:
                # 4. The person who loves beach vacations is in the first house.
                if p_vac[i_beach] != 0:
                    continue

                # 9. The person who prefers city breaks is somewhere to the right of Peter.
                if not (p_vac[i_city] > p_name[i_Peter]):
                    continue

                for p_hair in perms:
                    # 10. The person who has blonde hair is in the third house.
                    if p_hair[i_blonde] != 2:
                        continue

                    # 11. The person who loves beach vacations is the person who has brown hair.
                    if p_vac[i_beach] != p_hair[i_brown]:
                        continue

                    for p_flower in perms:
                        # 2. The person who loves a bouquet of daffodils is Arnold.
                        if p_name[i_Arnold] != p_flower[i_daffodils]:
                            continue

                        # 7. The person who loves the boquet of lilies is Eric.
                        if p_name[i_Eric] != p_flower[i_lilies]:
                            continue

                        for p_edu in perms:
                            # 5. The person with a high school diploma is in the third house.
                            if p_edu[i_high_school] != 2:
                                continue

                            # 8. The person who loves the boquet of lilies is the person with a bachelor's degree.
                            if p_flower[i_lilies] != p_edu[i_bachelor]:
                                continue

                            # If all constraints satisfied, build the solution table
                            by_house_name = invert_mapping(Names, p_name)
                            by_house_vac = invert_mapping(Vacations, p_vac)
                            by_house_height = invert_mapping(Heights, p_height)
                            by_house_flower = invert_mapping(Flowers, p_flower)
                            by_house_hair = invert_mapping(HairColors, p_hair)
                            by_house_edu = invert_mapping(Educations, p_edu)

                            rows = []
                            for h in range(3):
                                rows.append([
                                    str(h + 1),
                                    by_house_name[h],
                                    by_house_vac[h],
                                    by_house_height[h],
                                    by_house_flower[h],
                                    by_house_hair[h],
                                    by_house_edu[h],
                                ])
                            solutions.append(rows)

    # Expect a unique solution
    if not solutions:
        raise RuntimeError("No solution found.")
    if len(solutions) > 1:
        # In case multiple, just pick the first but this puzzle is expected to have a unique solution.
        rows = solutions[0]
    else:
        rows = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))