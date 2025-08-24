import itertools
import json

def solve_puzzle():
    houses = [1, 2]  # left to right

    Names = ["Eric", "Arnold"]
    HouseStyles = ["victorian", "colonial"]
    Heights = ["very short", "short"]
    Educations = ["associate", "high school"]

    solutions = []

    for name_perm in itertools.permutations(Names):
        for style_perm in itertools.permutations(HouseStyles):
            for height_perm in itertools.permutations(Heights):
                for edu_perm in itertools.permutations(Educations):
                    # Build assignments per house index (1-based)
                    assignments = {
                        h: {
                            "Name": name_perm[h-1],
                            "HouseStyle": style_perm[h-1],
                            "Height": height_perm[h-1],
                            "Education": edu_perm[h-1],
                        }
                        for h in houses
                    }

                    # Helper: find house number by attribute value
                    def find_house_by(attr, value):
                        for h in houses:
                            if assignments[h][attr] == value:
                                return h
                        return None

                    # Clue 1: The person who is short is directly left of Eric.
                    short_house = find_house_by("Height", "short")
                    eric_house = find_house_by("Name", "Eric")
                    if short_house is None or eric_house is None:
                        continue
                    if eric_house - short_house != 1:
                        continue

                    # Clue 2: The person residing in a Victorian house is in the first house.
                    if assignments[1]["HouseStyle"] != "victorian":
                        continue

                    # Clue 3: The person who is short is the person with an associate's degree.
                    if assignments[short_house]["Education"] != "associate":
                        continue

                    # If all constraints satisfied, record solution
                    solutions.append(assignments)

    if not solutions:
        raise ValueError("No solution found.")

    # Assuming a unique solution
    sol = solutions[0]
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": [
                [str(h), sol[h]["Name"], sol[h]["HouseStyle"], sol[h]["Height"], sol[h]["Education"]]
                for h in sorted(sol.keys())
            ],
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))