import itertools
import json

def main():
    names_list = ['Arnold', 'Eric', 'Peter']
    cigars_list = ['pall mall', 'blue master', 'prince']
    animals_list = ['horse', 'cat', 'bird']
    children_list = ['Bella', 'Fred', 'Meredith']
    bookgenres_list = ['science fiction', 'romance', 'mystery']
    phonemodels_list = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']

    for names in itertools.permutations(names_list):
        for cigars in itertools.permutations(cigars_list):
            if cigars[1] != 'pall mall':
                continue
            for animals in itertools.permutations(animals_list):
                for children in itertools.permutations(children_list):
                    for books in itertools.permutations(bookgenres_list):
                        if books[2] != 'science fiction':
                            continue
                        if books[1] == 'mystery':
                            continue
                        mystery_house = -1
                        for i in range(3):
                            if books[i] == 'mystery':
                                mystery_house = i
                                break
                        if mystery_house != -1 and children[mystery_house] != 'Fred':
                            continue
                        horse_ok = True
                        for i in range(3):
                            if animals[i] == 'horse' and children[i] != 'Meredith':
                                horse_ok = False
                                break
                        if not horse_ok:
                            continue
                        for phonemodels in itertools.permutations(phonemodels_list):
                            clue6 = False
                            for i in range(2):
                                if phonemodels[i] == 'iphone 13' and phonemodels[i+1] == 'samsung galaxy s21':
                                    clue6 = True
                                    break
                            if not clue6:
                                continue
                            sci_fi_house = 2
                            if phonemodels[sci_fi_house] != 'samsung galaxy s21':
                                continue
                            clue2 = True
                            for i in range(3):
                                if animals[i] == 'cat' and names[i] != 'Eric':
                                    clue2 = False
                                    break
                            if not clue2:
                                continue
                            clue5 = True
                            for i in range(3):
                                if children[i] == 'Bella' and cigars[i] != 'prince':
                                    clue5 = False
                                    break
                            if not clue5:
                                continue
                            fred_house = -1
                            for i in range(3):
                                if children[i] == 'Fred':
                                    fred_house = i
                                    break
                            if fred_house == -1 or fred_house == 2 or names[fred_house + 1] != 'Arnold':
                                continue
                            p_index = names.index('Peter')
                            e_index = names.index('Eric')
                            if p_index >= e_index:
                                continue
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                                    "rows": []
                                }
                            }
                            for i in range(3):
                                house_num = str(i + 1)
                                row = [
                                    house_num,
                                    names[i],
                                    cigars[i],
                                    animals[i],
                                    children[i],
                                    books[i],
                                    phonemodels[i]
                                ]
                                solution["solution"]["rows"].append(row)
                            print(json.dumps(solution))
                            return

if __name__ == "__main__":
    main()