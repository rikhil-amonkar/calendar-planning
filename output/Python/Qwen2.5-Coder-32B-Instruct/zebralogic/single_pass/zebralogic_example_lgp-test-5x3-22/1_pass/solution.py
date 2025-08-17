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
                # Assign permutations to houses
                house_info = list(zip(houses, name_perm, smoothie_perm, nationality_perm))

                # Check all constraints
                if (house_info[1][2] == "dragonfruit" and  # Clue 2
                    house_info.index(next(filter(lambda x: x[1] == "Eric", house_info)))[0] > 2 and  # Clue 1
                    house_info[0][1] != "Peter" and  # Clue 3
                    abs(house_info.index(next(filter(lambda x: x[3] == "dane", house_info)))[0] -
                        house_info.index(next(filter(lambda x: x[3] == "brit", house_info)))[0]) == 1 and  # Clue 4
                    house_info[4][2] != "desert" and  # Clue 5
                    house_info.index(next(filter(lambda x: x[3] == "swede", house_info)))[0] < 1 and  # Clue 6
                    abs(house_info.index(next(filter(lambda x: x[2] == "lime", house_info)))[0] -
                        house_info.index(next(filter(lambda x: x[3] == "dane", house_info)))[0]) == 3 and  # Clue 7
                    house_info[house_info.index(next(filter(lambda x: x[1] == "Bob", house_info)))[0] - 1][3] == "dane" and  # Clue 8
                    house_info[2][1] == "Alice" and  # Clue 9
                    house_info[2][0] == 3 and  # Clue 10
                    house_info[2][2] == "watermelon"):  # Clue 11

                    # Format the solution as required
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Smoothie", "Nationality"],
                            "rows": [[str(h), n, s, nat] for h, n, s, nat in house_info]
                        }
                    }
                    return json.dumps(solution)

# Solve the puzzle and print the solution
print(solve_puzzle())