import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    occupations = ["engineer", "doctor"]
    birthdays = ["april", "sept"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    cigars = ["pall mall", "prince"]

    # Generate all possible permutations for the two houses
    all_permutations = list(itertools.product(names, occupations, birthdays, house_styles, heights, cigars))

    # Filter permutations based on the given clues
    valid_solutions = []
    for perm1 in all_permutations:
        for perm2 in all_permutations:
            if perm1 != perm2:  # Ensure both houses are occupied by different people
                house1, house2 = perm1, perm2
                h1_name, h1_occupation, h1_birthday, h1_house_style, h1_height, h1_cigar = house1
                h2_name, h2_occupation, h2_birthday, h2_house_style, h2_height, h2_cigar = house2

                # Apply the clues
                if (h1_occupation == "engineer" and
                    h1_birthday == "april" != h2_birthday or h2_birthday == "april" != h1_birthday and
                    h1_house_style == "colonial" and
                    h1_height == "very short" and
                    h2_height == "short" and h2_cigar == "pall mall" and
                    h1_occupation == "engineer" and h1_name == "Eric"):
                    valid_solutions.append((house1, house2))

    # Format the solution as JSON
    if valid_solutions:
        solution = valid_solutions[0]  # Take the first valid solution
        formatted_solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                "rows": [
                    ["1"] + list(solution[0]),
                    ["2"] + list(solution[1])
                ]
            }
        }
        return json.dumps(formatted_solution, indent=2)
    else:
        return json.dumps({"solution": {"header": [], "rows": []}})

# Output the solution
print(solve_puzzle())