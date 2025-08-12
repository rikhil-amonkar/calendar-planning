import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Alice", "Peter", "Arnold", "Eric"]
    cigars = ["prince", "dunhill", "blue master", "pall mall"]
    sports = ["swimming", "basketball", "soccer", "tennis"]
    drinks = ["coffee", "water", "milk", "tea"]

    # Generate all possible permutations for each attribute
    permutations = list(itertools.permutations(range(4)))

    # Iterate through all possible combinations of permutations
    for name_order in permutations:
        for cigar_order in permutations:
            for sport_order in permutations:
                for drink_order in permutations:
                    # Assign the permutations to the attributes
                    house_names = {i + 1: names[name_order[i]] for i in range(4)}
                    house_cigars = {i + 1: cigars[cigar_order[i]] for i in range(4)}
                    house_sports = {i + 1: sports[sport_order[i]] for i in range(4)}
                    house_drinks = {i + 1: drinks[drink_order[i]] for i in range(4)}

                    # Check all the clues
                    if (house_names[4] == "Peter" and
                        house_drinks[house_sports.index("basketball")] == "tea" and
                        house_names[house_cigars.index("blue master")] == "Arnold" and
                        house_names[house_sports.index("basketball")] == "Eric" and
                        house_sports[house_cigars.index("blue master")] == "tennis" and
                        abs(house_drinks.index("water") - 4) == 2 and
                        house_drinks[house_names.index("Arnold")] == "coffee" and
                        house_sports.index("basketball") == 2 and
                        house_sports[house_cigars.index("prince")] == "soccer" and
                        house_cigars[house_names.index("Peter")] == "pall mall"):
                        
                        # Construct the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Cigar", "Sport", "Drink"],
                                "rows": []
                            }
                        }
                        for house in range(1, 5):
                            solution["solution"]["rows"].append([
                                str(house),
                                house_names[house],
                                house_cigars[house],
                                house_sports[house],
                                house_drinks[house]
                            ])
                        
                        # Output the solution as JSON
                        print(json.dumps(solution, indent=2))
                        return

# Run the solver
solve_puzzle()