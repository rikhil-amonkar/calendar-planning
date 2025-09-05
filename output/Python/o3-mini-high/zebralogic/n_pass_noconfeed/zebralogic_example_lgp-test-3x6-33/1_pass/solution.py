import itertools
import json

def main():
    names = ["Arnold", "Eric", "Peter"]
    flowers = ["carnations", "lilies", "daffodils"]
    haircolors = ["black", "brown", "blonde"]
    sports = ["soccer", "basketball", "tennis"]
    housestyles = ["colonial", "ranch", "victorian"]
    pets = ["fish", "dog", "cat"]

    # Houses are indexed as 0 (House 1), 1 (House 2), and 2 (House 3).
    for n in itertools.permutations(names):
        for f in itertools.permutations(flowers):
            # From Clue 7 deduction: the person who loves carnations must be immediately left of the blonde-haired person.
            # Since the blonde-haired person is in House 2 (Clue 2), the only possibility is House 1 having carnations.
            if f[0] != "carnations":
                continue
            for h in itertools.permutations(haircolors):
                # Clue 2: House 2 has blonde hair.
                if h[1] != "blonde":
                    continue
                for s in itertools.permutations(sports):
                    # Clue 8: The person who loves soccer is in House 3.
                    if s[2] != "soccer":
                        continue
                    for hs in itertools.permutations(housestyles):
                        # Clue 10: The person living in a colonial-style house is in House 3.
                        if hs[2] != "colonial":
                            continue
                        for p in itertools.permutations(pets):
                            valid = True
                            # Clue 1: The person who has a cat is the person who loves soccer.
                            for i in range(3):
                                if p[i] == "cat" and s[i] != "soccer":
                                    valid = False
                                    break
                                if s[i] == "soccer" and p[i] != "cat":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 3: The person who loves daffodils is the person who has blonde hair.
                            for i in range(3):
                                if f[i] == "daffodils" and h[i] != "blonde":
                                    valid = False
                                    break
                                if h[i] == "blonde" and f[i] != "daffodils":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 4: Peter is the person who loves basketball.
                            for i in range(3):
                                if n[i] == "Peter" and s[i] != "basketball":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 5: Arnold is directly left of the person in a ranch-style home.
                            found5 = False
                            for i in range(2):
                                if n[i] == "Arnold" and hs[i+1] == "ranch":
                                    found5 = True
                                    break
                            if not found5:
                                continue

                            # Clue 6: The person who owns a dog is the person who loves basketball.
                            for i in range(3):
                                if p[i] == "dog" and s[i] != "basketball":
                                    valid = False
                                    break
                                if s[i] == "basketball" and p[i] != "dog":
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 7: The person who loves carnations is directly left of the person who has blonde hair.
                            found7 = False
                            for i in range(2):
                                if f[i] == "carnations" and h[i+1] == "blonde":
                                    found7 = True
                                    break
                            if not found7:
                                continue

                            # Clue 9: Arnold is somewhere to the left of the person who has black hair.
                            posArnold = None
                            posBlack = None
                            for i in range(3):
                                if n[i] == "Arnold":
                                    posArnold = i
                                if h[i] == "black":
                                    posBlack = i
                            if posArnold is None or posBlack is None or posArnold >= posBlack:
                                continue

                            # If we have reached here, all constraints are satisfied.
                            # Prepare the solution rows for houses 1, 2, and 3.
                            solution = []
                            for i in range(3):
                                row = [str(i + 1), n[i], f[i], h[i], s[i], hs[i], p[i]]
                                solution.append(row)
                            
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                                    "rows": solution
                                }
                            }
                            print(json.dumps(result))
                            return

if __name__ == "__main__":
    main()