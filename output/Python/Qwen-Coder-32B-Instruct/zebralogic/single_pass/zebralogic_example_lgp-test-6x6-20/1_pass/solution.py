import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Alice", "Peter", "Eric", "Bob", "Arnold", "Carol"]
    cigars = ["pall mall", "yellow monster", "dunhill", "blue master", "prince", "blends"]
    music_genres = ["hip hop", "jazz", "country", "pop", "classical", "rock"]
    drinks = ["water", "milk", "boba tea", "tea", "root beer", "coffee"]
    mothers_names = ["Kailyn", "Penny", "Janelle", "Holly", "Sarah", "Aniya"]
    lunches = ["soup", "pizza", "spaghetti", "stir fry", "stew", "grilled cheese"]

    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            for music_perm in itertools.permutations(music_genres):
                for drink_perm in itertools.permutations(drinks):
                    for mother_perm in itertools.permutations(mothers_names):
                        for lunch_perm in itertools.permutations(lunches):
                            # Clue 1
                            if name_perm.index("Carol") + 1 != name_perm.index("Carol") + lunch_perm.index("grilled cheese"):
                                continue
                            # Clue 2
                            if name_perm[1] == "Eric":
                                continue
                            # Clue 3
                            if mother_perm.index("Holly") <= name_perm.index("Carol"):
                                continue
                            # Clue 4
                            if lunch_perm.index("grilled cheese") <= music_perm.index("rock"):
                                continue
                            # Clue 5
                            if name_perm.index("Eric") + 1 != name_perm.index("Carol"):
                                continue
                            # Clue 6
                            if music_perm[2] == "pop":
                                continue
                            # Clue 7
                            if music_perm[name_perm.index("Eric")] != "country":
                                continue
                            # Clue 8
                            if music_perm[5] != "classical":
                                continue
                            # Clue 9
                            if drink_perm[name_perm.index("Bob")] != "coffee":
                                continue
                            # Clue 10
                            if cigar_perm[name_perm.index("Peter")] != "blends":
                                continue
                            # Clue 11
                            if lunch_perm[4] == "stew":
                                continue
                            # Clue 12
                            if drink_perm.index("root beer") + 1 != mother_perm.index("Janelle"):
                                continue
                            # Clue 13
                            if abs(mother_perm.index("Sarah") - cigar_perm.index("yellow monster")) != 2:
                                continue
                            # Clue 14
                            if drink_perm[name_perm.index("Eric")] != "tea":
                                continue
                            # Clue 15
                            if cigar_perm.index("pall mall") <= lunch_perm.index("stir fry"):
                                continue
                            # Clue 16
                            if lunch_perm[name_perm.index("Bob")] != "soup":
                                continue
                            # Clue 17
                            if music_perm.index("hip hop") + 1 != mother_perm.index("Kailyn"):
                                continue
                            # Clue 18
                            if name_perm.index("Arnold") <= mother_perm.index("Kailyn"):
                                continue
                            # Clue 19
                            if drink_perm.index("water") + 1 != cigar_perm.index("blue master"):
                                continue
                            # Clue 20
                            if lunch_perm.index("spaghetti") >= cigar_perm.index("blends"):
                                continue
                            # Clue 21
                            if mother_perm.index("Sarah") + 1 != music_perm.index("jazz"):
                                continue
                            # Clue 22
                            if music_perm.index("hip hop") + 1 != drink_perm.index("root beer"):
                                continue
                            # Clue 23
                            if drink_perm[lunch_perm.index("stew")] != "water":
                                continue
                            # Clue 24
                            if cigar_perm[1] == "dunhill":
                                continue
                            # Clue 25
                            if drink_perm[mother_perm.index("Janelle")] != "milk":
                                continue
                            # Clue 26
                            if mother_perm[name_perm.index("Eric")] != "Aniya":
                                continue

                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Cigar", "Music Genre", "Drink", "Mother's Name", "Lunch"],
                                    "rows": []
                                }
                            }

                            for i in range(6):
                                solution["solution"]["rows"].append([
                                    str(houses[i]),
                                    name_perm[i],
                                    cigar_perm[i],
                                    music_perm[i],
                                    drink_perm[i],
                                    mother_perm[i],
                                    lunch_perm[i]
                                ])

                            return json.dumps(solution, indent=2)

print(solve_puzzle())