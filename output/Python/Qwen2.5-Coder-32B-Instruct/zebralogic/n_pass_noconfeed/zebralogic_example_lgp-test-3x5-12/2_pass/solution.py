import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = ['1', '2', '3']
    names = ['Eric', 'Peter', 'Arnold']
    cigars = ['blue master', 'prince', 'pall mall']
    hobbies = ['photography', 'gardening', 'cooking']
    educations = ['high school', 'associate', 'bachelor']
    drinks = ['tea', 'milk', 'water']

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(names_perm, cigars_perm, hobbies_perm, educations_perm, drinks_perm):
        # Create a dictionary to map each house to its attributes
        house_attributes = {
            '1': {'name': names_perm[0], 'cigar': cigars_perm[0], 'hobby': hobbies_perm[0],
                  'education': educations_perm[0], 'drink': drinks_perm[0]},
            '2': {'name': names_perm[1], 'cigar': cigars_perm[1], 'hobby': hobbies_perm[1],
                  'education': educations_perm[1], 'drink': drinks_perm[1]},
            '3': {'name': names_perm[2], 'cigar': cigars_perm[2], 'hobby': hobbies_perm[2],
                  'education': educations_perm[2], 'drink': drinks_perm[2]}
        }

        # Check each clue
        if house_attributes['1']['name'] == 'Peter' and house_attributes['1']['cigar'] != 'pall mall':
            return False
        if house_attributes['2']['name'] == 'Peter' and house_attributes['2']['cigar'] != 'pall mall':
            return False
        if house_attributes['3']['name'] == 'Peter' and house_attributes['3']['cigar'] != 'pall mall':
            return False
        if house_attributes[houses[drinks.index('milk')]]['education'] != 'high school':
            return False
        if house_attributes[houses[drinks.index('milk') + 1]]['education'] != 'high school':
            return False
        if house_attributes[houses[drinks.index('tea')]]['name'] != 'Eric':
            return False
        if abs(houses.index(str(names_perm.index('Arnold') + 1)) - houses.index(str(cigars.index('prince') + 1))) != 1:
            return False
        if houses.index(str(cigars.index('prince') + 1)) > houses.index(str(hobbies.index('gardening') + 1)):
            return False
        if house_attributes[houses[drinks.index('milk')]]['education'] != 'associate':
            return False
        if house_attributes[houses[educations.index('bachelor')]]['hobby'] != 'photography':
            return False
        if house_attributes[houses[educations.index('bachelor') + 1]]['hobby'] != 'photography':
            return False

        return True

    # Iterate over all permutations and find the valid solution
    for names_perm, cigars_perm, hobbies_perm, educations_perm, drinks_perm in itertools.product(
            itertools.permutations(names),
            itertools.permutations(cigars),
            itertools.permutations(hobbies),
            itertools.permutations(educations),
            itertools.permutations(drinks)
    ):
        if is_valid_solution(names_perm, cigars_perm, hobbies_perm, educations_perm, drinks_perm):
            solution = {
                "solution": {
                    "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                    "rows": [
                        ["1", names_perm[0], cigars_perm[0], hobbies_perm[0], educations_perm[0], drinks_perm[0]],
                        ["2", names_perm[1], cigars_perm[1], hobbies_perm[1], educations_perm[1], drinks_perm[1]],
                        ["3", names_perm[2], cigars_perm[2], hobbies_perm[2], educations_perm[2], drinks_perm[2]]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())