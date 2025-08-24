import json
from itertools import permutations

def solve_puzzle():
    houses = [1, 2, 3, 4]

    Names = ['Peter', 'Arnold', 'Eric', 'Alice']
    Flowers = ['daffodils', 'carnations', 'roses', 'lilies']
    Heights = ['very short', 'short', 'tall', 'average']
    Mothers = ['Janelle', 'Kailyn', 'Holly', 'Aniya']
    Occupations = ['engineer', 'doctor', 'teacher', 'artist']
    Sports = ['swimming', 'basketball', 'tennis', 'soccer']

    solution = None

    for name_perm in permutations(Names):
        # 9. Arnold is not in the third house.
        if name_perm[2] == 'Arnold':
            continue

        i_arn = name_perm.index('Arnold')
        i_peter = name_perm.index('Peter')
        i_eric = name_perm.index('Eric')
        i_alice = name_perm.index('Alice')

        for flower_perm in permutations(Flowers):
            # 13. Arnold loves lilies.
            if flower_perm[i_arn] != 'lilies':
                continue

            # 2. The person who loves roses is Eric.
            i_rose = flower_perm.index('roses')
            if name_perm[i_rose] != 'Eric':
                continue

            for height_perm in permutations(Heights):
                # 3. Arnold is tall.
                if height_perm[i_arn] != 'tall':
                    continue

                for mother_perm in permutations(Mothers):
                    # 7. Mother's name Janelle => carnations (same house)
                    if mother_perm.index('Janelle') != flower_perm.index('carnations'):
                        continue

                    # 12. Mother's name Aniya is Alice (same house)
                    if mother_perm.index('Aniya') != i_alice:
                        continue

                    # 10. Holly is somewhere to the right of average height.
                    if mother_perm.index('Holly') <= height_perm.index('average'):
                        continue

                    for occ_perm in permutations(Occupations):
                        # 6. Teacher is in the first house.
                        if occ_perm[0] != 'teacher':
                            continue

                        # 11. Peter is a doctor.
                        if occ_perm[i_peter] != 'doctor':
                            continue

                        # 4. Daffodils is somewhere to the right of engineer.
                        if flower_perm.index('daffodils') <= occ_perm.index('engineer'):
                            continue

                        for sport_perm in permutations(Sports):
                            # 1. Swimming <-> roses.
                            if sport_perm[i_rose] != 'swimming':
                                continue

                            # 5. Soccer <-> short.
                            if sport_perm[height_perm.index('short')] != 'soccer':
                                continue

                            # 8. Basketball <-> average.
                            if sport_perm[height_perm.index('average')] != 'basketball':
                                continue

                            # All constraints satisfied
                            solution = {
                                "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                                "rows": [
                                    [str(houses[i]), name_perm[i], flower_perm[i], height_perm[i], mother_perm[i], occ_perm[i], sport_perm[i]]
                                    for i in range(4)
                                ]
                            }
                            return solution

    return None

def main():
    result = solve_puzzle()
    if result is None:
        output = {"solution": {"header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"], "rows": []}}
    else:
        output = {"solution": result}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()