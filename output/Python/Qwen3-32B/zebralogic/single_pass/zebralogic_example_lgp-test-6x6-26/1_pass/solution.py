import itertools
import json

def solve_puzzle():
    names = ['Alice', 'Carol', 'Eric', 'Peter', 'Bob', 'Arnold']
    phones = ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9']
    cigars = ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster']
    flowers = ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris']
    colors = ['yellow', 'red', 'green', 'blue', 'white', 'purple']
    sports = ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']

    name_perms = [p for p in itertools.permutations(names) if p[0] == 'Alice']
    phone_perms = [p for p in itertools.permutations(phones) if p[1] == 'oneplus 9']

    for name in name_perms:
        carol_pos = None
        eric_pos = None
        for i in range(len(name)):
            if name[i] == 'Carol':
                carol_pos = i
            if name[i] == 'Eric':
                eric_pos = i
        if carol_pos is not None and eric_pos is not None and eric_pos == carol_pos + 1:
            pass
        else:
            continue

        for flower in itertools.permutations(flowers):
            if flower[carol_pos] != 'carnations':
                continue
            daffodils_pos = None
            for i in range(len(flower)):
                if flower[i] == 'daffodils':
                    daffodils_pos = i
                    break
            if abs(carol_pos - daffodils_pos) != 3:
                continue

            iris_pos = None
            for i in range(len(flower)):
                if flower[i] == 'iris':
                    iris_pos = i
                    break
            if iris_pos is not None and iris_pos >= eric_pos:
                continue

            for sport in itertools.permutations(sports):
                if sport[carol_pos] != 'soccer':
                    continue
                for color in itertools.permutations(colors):
                    yellow_pos = [i for i, c in enumerate(color) if c == 'yellow']
                    blue_pos = [i for i, c in enumerate(color) if c == 'blue']
                    if not any(abs(y - b) == 1 for y in yellow_pos for b in blue_pos):
                        continue

                    peter_pos = name.index('Peter')
                    if color[peter_pos] != 'blue':
                        continue

                    purple_pos = [i for i, c in enumerate(color) if c == 'purple']
                    if purple_pos:
                        p_pos = purple_pos[0]
                        if p_pos + 1 < len(cigars) and not any(p for p in itertools.permutations(cigars) if p[p_pos + 1] == 'pall mall'):
                            continue

                    for cigar in itertools.permutations(cigars):
                        if cigar[eric_pos] != 'blends':
                            continue
                        if cigar[name.index('Peter')] != 'dunhill':
                            continue

                        green_pos = [i for i, c in enumerate(color) if c == 'green']
                        if green_pos and cigar[green_pos[0]] != 'blue master':
                            continue

                        prince_pos = [i for i, c in enumerate(cigar) if c == 'prince']
                        if prince_pos and sport[prince_pos[0]] != 'basketball':
                            continue

                        dunhill_pos = [i for i, c in enumerate(cigar) if c == 'dunhill']
                        if dunhill_pos and sport[dunhill_pos[0]] != 'volleyball':
                            continue

                        volleyball_pos = [i for i, s in enumerate(sport) if s == 'volleyball']
                        if volleyball_pos and phones[volleyball_pos[0]] != 'iphone 13':
                            continue

                        google_pixel_pos = [i for i, p in enumerate(phones) if p == 'google pixel 6']
                        if google_pixel_pos and sport[google_pixel_pos[0]] != 'swimming':
                            continue

                        blends_pos = [i for i, c in enumerate(cigar) if c == 'blends']
                        if blends_pos and google_pixel_pos and google_pixel_pos[0] <= blends_pos[0]:
                            continue

                        blue_master_pos = [i for i, c in enumerate(cigar) if c == 'blue master']
                        if blue_master_pos:
                            bm_pos = blue_master_pos[0]
                            if bm_pos > 0 and sport[bm_pos - 1] != 'baseball':
                                continue

                        huawei_pos = [i for i, p in enumerate(phones) if p == 'huawei p50']
                        if huawei_pos:
                            h_pos = huawei_pos[0]
                            if h_pos + 1 < len(color) and color[h_pos + 1] != 'white':
                                continue

                        xiaomi_pos = [i for i, p in enumerate(phones) if p == 'xiaomi mi 11']
                        if xiaomi_pos and huawei_pos and xiaomi_pos[0] >= huawei_pos[0]:
                            continue

                        samsung_pos = [i for i, p in enumerate(phones) if p == 'samsung galaxy s21']
                        if samsung_pos and eric_pos < samsung_pos[0]:
                            continue

                        oneplus_pos = [i for i, p in enumerate(phones) if p == 'oneplus 9']
                        if oneplus_pos:
                            op_pos = oneplus_pos[0]
                            if not ((op_pos > 0 and flower[op_pos - 1] == 'roses') or (op_pos < len(flower) - 1 and flower[op_pos + 1] == 'roses')):
                                continue

                        bob_pos = name.index('Bob')
                        if flower[bob_pos] != 'tulips':
                            continue

                        solution = {
                            "solution": {
                                "header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"],
                                "rows": []
                            }
                        }
                        for i in range(6):
                            house = i + 1
                            solution["solution"]["rows"].append([
                                str(house),
                                name[i],
                                phones[i],
                                cigar[i],
                                flower[i],
                                color[i],
                                sport[i]
                            ])
                        return json.dumps(solution)
    return None

if __name__ == "__main__":
    result = solve_puzzle()
    if result:
        print(result)
    else:
        print("No solution found.")