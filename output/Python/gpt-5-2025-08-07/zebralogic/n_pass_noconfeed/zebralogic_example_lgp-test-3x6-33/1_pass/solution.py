import json
import itertools

def solve_puzzle():
    houses = [1, 2, 3]

    Names = ["Arnold", "Eric", "Peter"]
    Flowers = ["carnations", "lilies", "daffodils"]
    HairColors = ["black", "brown", "blonde"]
    FavoriteSports = ["soccer", "basketball", "tennis"]
    HouseStyles = ["colonial", "ranch", "victorian"]
    Pets = ["fish", "dog", "cat"]

    def pos(value, arrangement):
        return arrangement.index(value) + 1  # houses are 1-indexed

    for names in itertools.permutations(Names):
        # Constraint 9 (can only check once hair is known), and 5 (needs styles), so skip for now

        for flowers in itertools.permutations(Flowers):
            # Constraints 3 and 7 need hair; skip for now

            for hairs in itertools.permutations(HairColors):
                # 2. The person who has blonde hair is in the second house.
                if hairs[1] != "blonde":
                    continue

                # 3. Daffodils <-> blonde
                if pos("daffodils", flowers) != pos("blonde", hairs):
                    continue

                # 7. Carnations directly left of blonde
                if pos("carnations", flowers) != pos("blonde", hairs) - 1:
                    continue

                # 9. Arnold is somewhere to the left of the person who has black hair.
                if pos("Arnold", names) >= pos("black", hairs):
                    continue

                for sports in itertools.permutations(FavoriteSports):
                    # 8. The person who loves soccer is in the third house.
                    if pos("soccer", sports) != 3:
                        continue

                    # 4. Peter is the person who loves basketball.
                    if pos("Peter", names) != pos("basketball", sports):
                        continue

                    for styles in itertools.permutations(HouseStyles):
                        # 10. Colonial-style house is in the third house.
                        if pos("colonial", styles) != 3:
                            continue

                        # 5. Arnold is directly left of the person in a ranch-style home.
                        if pos("Arnold", names) != pos("ranch", styles) - 1:
                            continue

                        for pets in itertools.permutations(Pets):
                            # 1. cat <-> soccer
                            if pos("cat", pets) != pos("soccer", sports):
                                continue

                            # 6. dog <-> basketball
                            if pos("dog", pets) != pos("basketball", sports):
                                continue

                            # Found a valid solution
                            rows = []
                            for h in houses:
                                rows.append([
                                    str(h),
                                    names[h-1],
                                    flowers[h-1],
                                    hairs[h-1],
                                    sports[h-1],
                                    styles[h-1],
                                    pets[h-1],
                                ])

                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                                    "rows": rows
                                }
                            }
                            return result

    # If no solution found (should not happen for a well-posed puzzle)
    return {
        "solution": {
            "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
            "rows": []
        }
    }

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))