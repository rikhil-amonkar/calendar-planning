import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]

    names_list = ["Eric", "Peter", "Arnold"]
    cigars_list = ["blue master", "prince", "pall mall"]
    hobbies_list = ["photography", "gardening", "cooking"]
    educations_list = ["high school", "associate", "bachelor"]
    drinks_list = ["tea", "milk", "water"]

    def pos(arr, value):
        return arr.index(value)

    solutions = []

    for names in itertools.permutations(names_list):
        for cigars in itertools.permutations(cigars_list):
            # 1. The person partial to Pall Mall is Peter.
            if pos(names, "Peter") != pos(cigars, "pall mall"):
                continue
            # 4. Arnold and the Prince smoker are next to each other.
            if abs(pos(names, "Arnold") - pos(cigars, "prince")) != 1:
                continue

            for hobbies in itertools.permutations(hobbies_list):
                # 5. Gardening is somewhere to the left of the Prince smoker.
                if not (pos(hobbies, "gardening") < pos(cigars, "prince")):
                    continue

                for educations in itertools.permutations(educations_list):
                    # 7. The person with a bachelor's degree is directly left of the photography enthusiast.
                    if pos(educations, "bachelor") + 1 != pos(hobbies, "photography"):
                        continue

                    for drinks in itertools.permutations(drinks_list):
                        # 2. Milk is directly left of high school.
                        if pos(drinks, "milk") + 1 != pos(educations, "high school"):
                            continue
                        # 6. Milk is associate's degree.
                        if pos(drinks, "milk") != pos(educations, "associate"):
                            continue
                        # 3. Eric is the tea drinker.
                        if pos(names, "Eric") != pos(drinks, "tea"):
                            continue

                        solutions.append((names, cigars, hobbies, educations, drinks))

    if len(solutions) != 1:
        raise RuntimeError(f"Expected a unique solution, found {len(solutions)}")

    names, cigars, hobbies, educations, drinks = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
            "rows": []
        }
    }

    for i in range(3):
        row = [
            str(houses[i]),
            names[i],
            cigars[i],
            hobbies[i],
            educations[i],
            drinks[i]
        ]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()