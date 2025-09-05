import itertools
import json

def main():
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    educations = ["associate", "high school"]

    solution = None

    # There are 2 houses, indexed as 0 and 1 corresponding to House 1 and House 2.
    for names_perm in itertools.permutations(names):
        for house_styles_perm in itertools.permutations(house_styles):
            # Constraint 2: The person residing in a Victorian house is in the first house.
            if house_styles_perm[0] != "victorian":
                continue
            for heights_perm in itertools.permutations(heights):
                for educations_perm in itertools.permutations(educations):
                    # Constraint 3: The person who is short is the person with an associate's degree.
                    # The index in the heights list where "short" appears must be the same index 
                    # where "associate" appears in the educations list.
                    if heights_perm.index("short") != educations_perm.index("associate"):
                        continue

                    # Constraint 1: The person who is short is directly left of Eric.
                    try:
                        index_eric = names_perm.index("Eric")
                    except ValueError:
                        continue
                    # Eric must not be in the first house (index 0) since someone is directly to his left.
                    if index_eric == 0:
                        continue
                    # The house immediately to the left of Eric must be occupied by the person who is "short".
                    if heights_perm[index_eric - 1] != "short":
                        continue

                    # All constraints are satisfied, so we record the solution.
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                            "rows": [
                                ["1", names_perm[0], house_styles_perm[0], heights_perm[0], educations_perm[0]],
                                ["2", names_perm[1], house_styles_perm[1], heights_perm[1], educations_perm[1]]
                            ]
                        }
                    }
                    break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    # If no solution was found (should not happen), output an empty rows list.
    if solution is None:
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                "rows": []
            }
        }

    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()