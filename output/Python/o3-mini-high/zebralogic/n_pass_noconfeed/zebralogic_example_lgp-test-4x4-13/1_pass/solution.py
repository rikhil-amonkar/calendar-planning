import itertools
import json

def main():
    # Define the domains for each attribute
    names = ["Alice", "Peter", "Arnold", "Eric"]
    cigars = ["prince", "dunhill", "blue master", "pall mall"]
    sports = ["swimming", "basketball", "soccer", "tennis"]
    drinks = ["coffee", "water", "milk", "tea"]

    # There are 4 houses with indices 0-3 corresponding to houses 1-4.
    # Apply constraints in the nested loops.
    for names_perm in itertools.permutations(names):
        # Clue 1: Peter is in the fourth house (index 3)
        if names_perm[3] != "Peter":
            continue

        # Pre-calculate indices for special names
        try:
            index_arnold = names_perm.index("Arnold")
            index_peter = names_perm.index("Peter")
        except ValueError:
            continue

        for cigars_perm in itertools.permutations(cigars):
            # Clue 3: Arnold smokes Blue Master.
            if cigars_perm[index_arnold] != "blue master":
                continue
            # Clue 10: Peter is partial to Pall Mall.
            if cigars_perm[index_peter] != "pall mall":
                continue

            for sports_perm in itertools.permutations(sports):
                # Clue 8: The person who loves basketball is in the third house (index 2).
                if sports_perm[2] != "basketball":
                    continue
                # Clue 4: The person who loves basketball is Eric.
                if names_perm[2] != "Eric":
                    continue
                # Clue 5: The person who loves tennis is the person who smokes Blue Master.
                if sports_perm[index_arnold] != "tennis":
                    continue
                # Clue 9: The Prince smoker is the person who loves soccer.
                valid_prince = True
                for i in range(4):
                    if cigars_perm[i] == "prince" and sports_perm[i] != "soccer":
                        valid_prince = False
                        break
                if not valid_prince:
                    continue

                for drinks_perm in itertools.permutations(drinks):
                    # Clue 6: There are two houses between the one who drinks water and Peter.
                    # This means the water drinker and Peter must be 3 houses apart.
                    if abs(drinks_perm.index("water") - index_peter) != 3:
                        continue
                    # Clue 7: The coffee drinker is Arnold.
                    if drinks_perm[index_arnold] != "coffee":
                        continue
                    # Clue 2: The tea drinker is the person who loves basketball.
                    # Since basketball is in house 3 (index2), that house must have tea.
                    if drinks_perm[2] != "tea":
                        continue

                    # If all constraints are satisfied, build the solution.
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                            "rows": []
                        }
                    }
                    for i in range(4):
                        # Houses are numbered 1 to 4.
                        row = [str(i + 1), names_perm[i], cigars_perm[i], sports_perm[i], drinks_perm[i]]
                        solution["solution"]["rows"].append(row)
                    
                    print(json.dumps(solution))
                    return

if __name__ == "__main__":
    main()