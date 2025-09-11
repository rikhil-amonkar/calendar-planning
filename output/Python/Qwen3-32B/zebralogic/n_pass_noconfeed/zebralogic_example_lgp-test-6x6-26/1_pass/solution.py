import itertools
import json

names = ['Alice', 'Bob', 'Carol', 'Eric', 'Peter', 'Arnold']
phones = ['huawei p50', 'google pixel 6', 'xiaomi mi 11', 'iphone 13', 'samsung galaxy s21', 'oneplus 9']
cigars = ['dunhill', 'pall mall', 'blends', 'blue master', 'prince', 'yellow monster']
flowers = ['daffodils', 'carnations', 'roses', 'tulips', 'lilies', 'iris']
colors = ['yellow', 'red', 'green', 'blue', 'white', 'purple']
sports = ['soccer', 'tennis', 'basketball', 'volleyball', 'swimming', 'baseball']

for names_perm in itertools.permutations(names):
    if names_perm[0] != 'Alice':
        continue
    try:
        i_carol = names_perm.index('Carol')
        i_eric = names_perm.index('Eric')
    except ValueError:
        continue
    if i_eric != i_carol + 1:
        continue
    daffodils_pos = None
    if i_carol + 3 <= 5:
        daffodils_pos = i_carol + 3
    elif i_carol - 3 >= 0:
        daffodils_pos = i_carol - 3
    else:
        continue
    for flowers_perm in itertools.permutations(flowers):
        if flowers_perm[i_carol] != 'carnations':
            continue
        i_bob = names_perm.index('Bob')
        if flowers_perm[i_bob] != 'tulips':
            continue
        if flowers_perm[daffodils_pos] != 'daffodils':
            continue
        iris_pos = flowers_perm.index('iris')
        if iris_pos >= i_eric:
            continue
        if flowers_perm[0] != 'roses' and flowers_perm[2] != 'roses':
            continue
        for sports_perm in itertools.permutations(sports):
            if sports_perm[i_carol] != 'soccer':
                continue
            i_peter = names_perm.index('Peter')
            if sports_perm[i_peter] != 'volleyball':
                continue
            for phones_perm in itertools.permutations(phones):
                if phones_perm[1] != 'oneplus 9':
                    continue
                if phones_perm[i_peter] != 'iphone 13':
                    continue
                i_samsung = phones_perm.index('samsung galaxy s21')
                if i_samsung >= i_eric:
                    continue
                i_google = phones_perm.index('google pixel 6')
                if i_google <= i_eric:
                    continue
                if sports_perm[i_google] != 'swimming':
                    continue
                i_xiaomi = phones_perm.index('xiaomi mi 11')
                i_huawei = phones_perm.index('huawei p50')
                if i_xiaomi >= i_huawei:
                    continue
                for colors_perm in itertools.permutations(colors):
                    if colors_perm[i_peter] != 'blue':
                        continue
                    if i_huawei + 1 > 5 or colors_perm[i_huawei + 1] != 'white':
                        continue
                    i_blue = i_peter
                    found_yellow_adjacent = False
                    if i_blue > 0 and colors_perm[i_blue - 1] == 'yellow':
                        found_yellow_adjacent = True
                    if i_blue < 5 and colors_perm[i_blue + 1] == 'yellow':
                        found_yellow_adjacent = True
                    if not found_yellow_adjacent:
                        continue
                    for cigars_perm in itertools.permutations(cigars):
                        if cigars_perm[i_eric] != 'blends':
                            continue
                        if cigars_perm[i_peter] != 'dunhill':
                            continue
                        found_invalid = False
                        for i in range(6):
                            if colors_perm[i] == 'green' and cigars_perm[i] != 'blue master':
                                found_invalid = True
                                break
                        if found_invalid:
                            continue
                        found_invalid = False
                        for i in range(6):
                            if sports_perm[i] == 'baseball':
                                if i + 1 > 5 or cigars_perm[i + 1] != 'blue master':
                                    found_invalid = True
                                    break
                        if found_invalid:
                            continue
                        found_invalid = False
                        for i in range(6):
                            if cigars_perm[i] == 'prince' and sports_perm[i] != 'basketball':
                                found_invalid = True
                                break
                        if found_invalid:
                            continue
                        found_invalid = False
                        for i in range(6):
                            if colors_perm[i] == 'purple':
                                if i + 1 > 5 or cigars_perm[i + 1] != 'pall mall':
                                    found_invalid = True
                                    break
                        if found_invalid:
                            continue
                        solution = []
                        for i in range(6):
                            house = str(i + 1)
                            name = names_perm[i]
                            phone = phones_perm[i]
                            cigar = cigars_perm[i]
                            flower = flowers_perm[i]
                            color = colors_perm[i]
                            sport = sports_perm[i]
                            solution.append([house, name, phone, cigar, flower, color, sport])
                        print(json.dumps({"solution": {"header": ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"], "rows": solution}}))
                        exit()