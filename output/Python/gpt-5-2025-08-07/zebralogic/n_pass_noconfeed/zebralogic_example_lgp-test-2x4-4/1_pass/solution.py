import itertools
import json

def solve_puzzle():
    # Houses are ordered left (1) to right (2), as seen from across the street
    houses = [1, 2]

    # Attributes (input variables)
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    educations = ["associate", "high school"]

    solutions = []

    # Generate all bijective assignments via permutations
    for name_assign in itertools.permutations(names):
        # Clue 1 pre-check: the short person is directly left of Eric, so Eric cannot be in the first house
        # If Eric is in the first house (index 0), skip early
        if name_assign.index("Eric") == 0:
            continue

        for style_assign in itertools.permutations(house_styles):
            # Clue 2: The person residing in a Victorian house is in the first house.
            if style_assign[0] != "victorian":
                continue

            for height_assign in itertools.permutations(heights):
                # Clue 1: The person who is short is directly left of Eric.
                try:
                    idx_short = height_assign.index("short")
                    idx_eric = name_assign.index("Eric")
                except ValueError:
                    continue
                if idx_short + 1 != idx_eric:
                    continue

                for edu_assign in itertools.permutations(educations):
                    # Clue 3: The person who is short is the person with an associate's degree.
                    try:
                        idx_assoc = edu_assign.index("associate")
                    except ValueError:
                        continue
                    if idx_short != idx_assoc:
                        continue

                    # All constraints satisfied; record solution
                    solution_rows = []
                    for i, h in enumerate(houses):
                        solution_rows.append([
                            str(h),
                            name_assign[i],
                            style_assign[i],
                            height_assign[i],
                            edu_assign[i],
                        ])
                    solutions.append(solution_rows)

    # Choose the unique solution if available
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")
    # If multiple solutions exist (shouldn't for a well-posed puzzle), take the first
    final_rows = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": final_rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))