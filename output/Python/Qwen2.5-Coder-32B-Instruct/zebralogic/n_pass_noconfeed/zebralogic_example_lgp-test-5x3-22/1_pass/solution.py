import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for smoothie_perm in itertools.permutations(smoothies):
            for nationality_perm in itertools.permutations(nationalities):
                # Create a list of dictionaries for each house
                houses_data = [
                    {"house": h, "name": n, "smoothie": s, "nationality": nat}
                    for h, n, s, nat in zip(houses, name_perm, smoothie_perm, nationality_perm)
                ]

                # Check all constraints
                if (houses_data[1]["smoothie"] == "dragonfruit" and  # Clue 2
                    houses_data.index(next(h for h in houses_data if h["name"] == "Eric")) >  # Clue 1
                    houses_data.index(next(h for h in houses_data if h["smoothie"] == "dragonfruit")) and
                    houses_data[0]["name"] != "Peter" and  # Clue 3
                    abs(houses_data.index(next(h for h in houses_data if h["nationality"] == "dane")) -
                        houses_data.index(next(h for h in houses_data if h["nationality"] == "brit"))) == 1 and  # Clue 4
                    houses_data[4]["smoothie"] != "desert" and  # Clue 5
                    houses_data.index(next(h for h in houses_data if h["nationality"] == "swede")) <  # Clue 6
                    houses_data.index(next(h for h in houses_data if h["smoothie"] == "dragonfruit")) and
                    abs(houses_data.index(next(h for h in houses_data if h["smoothie"] == "lime")) -
                        houses_data.index(next(h for h in houses_data if h["nationality"] == "dane"))) == 3 and  # Clue 7
                    houses_data[houses_data.index(next(h for h in houses_data if h["name"] == "Bob"))]["nationality"] == "dane" and  # Clue 8
                    houses_data[houses_data.index(next(h for h in houses_data if h["name"] == "Alice"))]["nationality"] == "norwegian" and  # Clue 9
                    houses_data[2]["name"] == "Alice" and  # Clue 10
                    houses_data[2]["smoothie"] == "watermelon"):  # Clue 11

                    # If all constraints are satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Nationality"],
                            "rows": [[str(h["house"]), h["name"], h["smoothie"], h["nationality"]] for h in houses_data]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())