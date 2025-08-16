import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = [1, 2, 3, 4]
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    cigars = ['prince', 'dunhill', 'blue master', 'pall mall']
    sports = ['swimming', 'basketball', 'soccer', 'tennis']
    drinks = ['coffee', 'water', 'milk', 'tea']

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(names))
    all_permutations.extend(list(itertools.permutations(cigars)))
    all_permutations.extend(list(itertools.permutations(sports)))
    all_permutations.extend(list(itertools.permutations(drinks)))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(name_perm, cigar_perm, sport_perm, drink_perm):
        # Create a dictionary to map each house to its attributes
        house_attributes = {house: {} for house in houses}
        for i in range(4):
            house_attributes[houses[i]]['Name'] = name_perm[i]
            house_attributes[houses[i]]['Cigar'] = cigar_perm[i]
            house_attributes[houses[i]]['FavoriteSport'] = sport_perm[i]
            house_attributes[houses[i]]['Drink'] = drink_perm[i]

        # Check each clue
        if house_attributes[4]['Name'] != 'Peter':
            return False
        if house_attributes[drink_perm.index('tea')]['FavoriteSport'] != 'basketball':
            return False
        if house_attributes[cigar_perm.index('blue master')]['Name'] != 'Arnold':
            return False
        if house_attributes[sport_perm.index('basketball')]['Name'] != 'Eric':
            return False
        if house_attributes[cigar_perm.index('blue master')]['FavoriteSport'] != 'tennis':
            return False
        if abs(house_attributes[drink_perm.index('water')] - 4) != 2:
            return False
        if house_attributes[name_perm.index('Arnold')]['Drink'] != 'coffee':
            return False
        if house_attributes[3]['FavoriteSport'] != 'basketball':
            return False
        if house_attributes[cigar_perm.index('prince')]['FavoriteSport'] != 'soccer':
            return False
        if house_attributes[name_perm.index('Peter')]['Cigar'] != 'pall mall':
            return False

        return True

    # Iterate through all permutations to find the valid solution
    for name_perm in itertools.permutations(names):
        for cigar_perm in itertools.permutations(cigars):
            for sport_perm in itertools.permutations(sports):
                for drink_perm in itertools.permutations(drinks):
                    if is_valid_solution(name_perm, cigar_perm, sport_perm, drink_perm):
                        # Construct the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
                                "rows": []
                            }
                        }
                        for house in houses:
                            row = [str(house)]
                            row.append(house_attributes[house]['Name'])
                            row.append(house_attributes[house]['Cigar'])
                            row.append(house_attributes[house]['FavoriteSport'])
                            row.append(house_attributes[house]['Drink'])
                            solution["solution"]["rows"].append(row)
                        return json.dumps(solution)

# Solve the puzzle and print the result
print(solve_puzzle())