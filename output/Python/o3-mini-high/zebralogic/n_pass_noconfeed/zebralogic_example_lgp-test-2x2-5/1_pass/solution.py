import json
import itertools

def main():
    houses = [1, 2]
    possible_names = ["Eric", "Arnold"]
    possible_styles = ["victorian", "colonial"]
    
    solution = None

    # Iterate over all possible assignments of names and house styles
    for names in itertools.permutations(possible_names):
        # Clue 2: Eric is in the first house.
        if names[0] != "Eric":
            continue
        for styles in itertools.permutations(possible_styles):
            # Clue 1: The person residing in a Victorian house is somewhere to the left of the person living in a colonial-style house.
            if styles.index("victorian") >= styles.index("colonial"):
                continue
            # Found a valid solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "HouseStyle"],
                    "rows": [
                        [str(houses[0]), names[0], styles[0]],
                        [str(houses[1]), names[1], styles[1]]
                    ]
                }
            }
            break
        if solution:
            break

    print(json.dumps(solution))

if __name__ == '__main__':
    main()