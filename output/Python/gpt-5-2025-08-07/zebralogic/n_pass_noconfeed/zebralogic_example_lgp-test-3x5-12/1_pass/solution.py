import json
from itertools import permutations

def solve_puzzle():
    # Houses are ordered 1..3 from left to right
    houses = [1, 2, 3]

    # Attributes
    names = ["Eric", "Peter", "Arnold"]
    cigars = ["blue master", "prince", "pall mall"]
    hobbies = ["photography", "gardening", "cooking"]
    educations = ["high school", "associate", "bachelor"]
    drinks = ["tea", "milk", "water"]

    solutions = []

    for name in permutations(names):
        for cigar in permutations(cigars):
            # 1. The person partial to Pall Mall is Peter.
            if name.index("Peter") != cigar.index("pall mall"):
                continue

            # 4. Arnold and the Prince smoker are next to each other.
            if abs(name.index("Arnold") - cigar.index("prince")) != 1:
                continue

            # 5. The person who enjoys gardening is somewhere to the left of the Prince smoker.
            # We can only check after hobby is chosen, so postpone

            for drink in permutations(drinks):
                # 3. Eric is the tea drinker.
                if name.index("Eric") != drink.index("tea"):
                    continue

                for education in permutations(educations):
                    # 2. Milk is directly left of High School.
                    if drink.index("milk") != education.index("high school") - 1:
                        continue

                    # 6. Milk drinker has associate's degree.
                    if drink.index("milk") != education.index("associate"):
                        continue

                    for hobby in permutations(hobbies):
                        # 7. Bachelor's is directly left of Photography.
                        if education.index("bachelor") != hobby.index("photography") - 1:
                            continue

                        # 5. Gardening is somewhere to the left of Prince smoker.
                        if hobby.index("gardening") >= cigar.index("prince"):
                            continue

                        # All constraints satisfied; record solution
                        rows = []
                        for i in range(3):
                            rows.append([
                                str(i + 1),
                                name[i],
                                cigar[i],
                                hobby[i],
                                education[i],
                                drink[i],
                            ])
                        solutions.append(rows)

    # Prepare output JSON. Use the first solution if multiple.
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    result = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
            "rows": solutions[0]
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))