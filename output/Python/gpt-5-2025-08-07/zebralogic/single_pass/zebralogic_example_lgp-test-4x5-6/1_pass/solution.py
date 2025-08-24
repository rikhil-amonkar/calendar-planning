import itertools
import json

def solve():
    houses = [1, 2, 3, 4]

    Names = ["Peter", "Eric", "Alice", "Arnold"]
    Education = ["bachelor", "high school", "associate", "master"]
    Music = ["jazz", "rock", "pop", "classical"]
    Colors = ["green", "red", "yellow", "white"]
    Flowers = ["lilies", "carnations", "daffodils", "roses"]

    solutions = []

    # Helper to create a mapping from attribute value to house number given a permutation of houses
    def make_map(values, perm):
        return {values[i]: perm[i] for i in range(4)}

    for colors_perm in itertools.permutations(houses):
        cpos = make_map(Colors, colors_perm)
        # Clue 11: red directly left of white
        if not (cpos["red"] + 1 == cpos["white"]):
            continue
        # Clue 7 implies yellow is not in the 4th house (since it must be directly left of roses)
        if cpos["yellow"] == 4:
            continue

        for flowers_perm in itertools.permutations(houses):
            fpos = make_map(Flowers, flowers_perm)
            # Clue 2 and 10: carnations not in 1st or 4th house
            if fpos["carnations"] in (1, 4):
                continue
            # Clue 7: yellow directly left of roses
            if not (cpos["yellow"] + 1 == fpos["roses"]):
                continue
            # Clue 14: daffodils = yellow
            if not (fpos["daffodils"] == cpos["yellow"]):
                continue

            for educ_perm in itertools.permutations(houses):
                epos = make_map(Education, educ_perm)
                # Clue 1: bachelor = daffodils
                if epos["bachelor"] != fpos["daffodils"]:
                    continue
                # Clue 9: associate not in 4th
                if epos["associate"] == 4:
                    continue

                for music_perm in itertools.permutations(houses):
                    mpos = make_map(Music, music_perm)
                    # Clue 8: pop in 2nd house
                    if mpos["pop"] != 2:
                        continue
                    # Clue 12: red = rock
                    if mpos["rock"] != cpos["red"]:
                        continue
                    # Clue 4: master directly left of classical
                    if not (epos["master"] + 1 == mpos["classical"]):
                        continue

                    for names_perm in itertools.permutations(houses):
                        npos = make_map(Names, names_perm)
                        # Clue 5: Eric not in 2nd
                        if npos["Eric"] == 2:
                            continue
                        # Clue 6: Arnold not in 3rd
                        if npos["Arnold"] == 3:
                            continue
                        # Clue 13: Arnold = yellow
                        if npos["Arnold"] != cpos["yellow"]:
                            continue
                        # Clue 3: Alice = master
                        if npos["Alice"] != epos["master"]:
                            continue

                        # If all constraints satisfied, build the solution grid
                        rows = []
                        for h in houses:
                            # Find values for each attribute at house h
                            name = next(v for v in Names if npos[v] == h)
                            educ = next(v for v in Education if epos[v] == h)
                            music = next(v for v in Music if mpos[v] == h)
                            color = next(v for v in Colors if cpos[v] == h)
                            flower = next(v for v in Flowers if fpos[v] == h)
                            rows.append([str(h), name, educ, music, color, flower])

                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                                "rows": rows
                            }
                        }
                        solutions.append(solution)

    # Return the first solution found (the puzzle should have a unique solution)
    if solutions:
        return solutions[0]
    else:
        # If no solution found, still return structure with empty rows to keep JSON valid
        return {
            "solution": {
                "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                "rows": []
            }
        }

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, ensure_ascii=False, indent=2))