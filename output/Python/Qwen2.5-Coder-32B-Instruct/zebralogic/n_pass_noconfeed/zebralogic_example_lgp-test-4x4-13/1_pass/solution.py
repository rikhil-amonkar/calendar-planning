import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Alice", "Peter", "Arnold", "Eric"]
    cigars = ["prince", "dunhill", "blue master", "pall mall"]
    sports = ["swimming", "basketball", "soccer", "tennis"]
    drinks = ["coffee", "water", "milk", "tea"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            for sport_perm in itertools.permutations(sports):
                for drink_perm in itertools.permutations(drinks):
                    # Assign permutations to houses
                    house_info = list(zip(houses, name_perm, cigar_perm, sport_perm, drink_perm))

                    # Check constraints
                    if (house_info[3][1] == "Peter" and  # Peter is in the fourth house
                        house_info[[sport for sport in range(4) if sport_perm[sport] == "basketball"][0]][4] == "tea" and  # The tea drinker is the person who loves basketball
                        house_info[[cigar for cigar in range(4) if cigar_perm[cigar] == "blue master"][0]][1] == "Arnold" and  # Arnold is the person who smokes Blue Master
                        house_info[[sport for sport in range(4) if sport_perm[sport] == "basketball"][0]][1] == "Eric" and  # The person who loves basketball is Eric
                        house_info[[cigar for cigar in range(4) if cigar_perm[cigar] == "blue master"][0]][3] == "tennis" and  # The person who loves tennis is the person who smokes Blue Master
                        abs([drink for drink in range(4) if drink_perm[drink] == "water"][0] - 3) == 2 and  # There are two houses between the one who only drinks water and Peter
                        house_info[[name for name in range(4) if name_perm[name] == "Arnold"][0]][4] == "coffee" and  # The coffee drinker is Arnold
                        house_info[2][3] == "basketball" and  # The person who loves basketball is in the third house
                        house_info[[cigar for cigar in range(4) if cigar_perm[cigar] == "prince"][0]][3] == "soccer" and  # The Prince smoker is the person who loves soccer
                        house_info[3][2] == "pall mall"):  # Peter is the person partial to Pall Mall

                        # Format the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                                "rows": [[str(house), name, cigar, sport, drink] for house, name, cigar, sport, drink in house_info]
                            }
                        }

                        return json.dumps(solution, indent=2)

# Solve and print the puzzle
print(solve_puzzle())