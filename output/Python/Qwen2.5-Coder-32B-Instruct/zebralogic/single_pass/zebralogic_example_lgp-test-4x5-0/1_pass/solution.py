import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = ['1', '2', '3', '4']
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phone_models = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(smoothies)) + \
                       list(itertools.permutations(cigars)) + \
                       list(itertools.permutations(heights)) + \
                       list(itertools.permutations(phone_models))

    # Iterate through all combinations of permutations
    for names_perm, smoothies_perm, cigars_perm, heights_perm, phone_models_perm in itertools.product(all_permutations, repeat=5):
        # Create a dictionary to store the current combination
        current_solution = {
            house: {
                'Name': name,
                'Smoothie': smoothie,
                'Cigar': cigar,
                'Height': height,
                'PhoneModel': phone_model
            }
            for house, name, smoothie, cigar, height, phone_model in zip(houses, names_perm, smoothies_perm, cigars_perm, heights_perm, phone_models_perm)
        }

        # Check all the clues
        if (current_solution['1']['Name'] == 'Eric' and current_solution['1']['Smoothie'] == 'dragonfruit') and \
           (current_solution[i]['Cigar'] == 'dunhill' and current_solution[i]['Smoothie'] == 'cherry' for i in range(4) if current_solution[i]['Cigar'] == 'dunhill') and \
           (current_solution[houses.index(str(i))]['PhoneModel'] == 'samsung galaxy s21' and current_solution[houses.index(str(i+1))]['PhoneModel'] == 'iphone 13' for i in range(3) if current_solution[houses.index(str(i))]['PhoneModel'] == 'samsung galaxy s21') and \
           (current_solution[houses.index(str(i))]['Cigar'] == 'dunhill' and current_solution[houses.index(str(j))]['Height'] == 'very short' for i in range(4) for j in range(i+1, 4) if current_solution[houses.index(str(i))]['Cigar'] == 'dunhill') and \
           (current_solution[houses.index(str(i))]['Smoothie'] == 'watermelon' and current_solution[houses.index(str(j))]['Smoothie'] == 'desert' for i in range(4) for j in range(i+1, 4) if current_solution[houses.index(str(i))]['Smoothie'] == 'watermelon') and \
           (current_solution[i]['Cigar'] == 'prince' and current_solution[i]['PhoneModel'] == 'oneplus 9' for i in range(4) if current_solution[i]['Cigar'] == 'prince') and \
           (current_solution['3']['Height'] == 'tall') and \
           (current_solution[i]['PhoneModel'] == 'iphone 13' and current_solution[i]['Height'] == 'very short' for i in range(4) if current_solution[i]['PhoneModel'] == 'iphone 13') and \
           (current_solution[i]['Cigar'] != 'blue master' for i in range(1, 4) if current_solution[i]['Cigar'] == 'blue master') and \
           (current_solution[i]['Cigar'] == 'dunhill' and current_solution[i]['Height'] == 'short' for i in range(4) if current_solution[i]['Cigar'] == 'dunhill') and \
           (current_solution[i]['Name'] != 'Peter' for i in range(4) if current_solution[i]['House'] == '3') and \
           (current_solution[i]['Name'] == 'Arnold' and current_solution[i]['PhoneModel'] == 'google pixel 6' for i in range(4) if current_solution[i]['Name'] == 'Arnold') and \
           (current_solution[i]['Name'] == 'Eric' and current_solution[i]['Cigar'] == 'pall mall' for i in range(4) if current_solution[i]['Name'] == 'Eric'):
            # If all clues are satisfied, format the solution as required
            solution_rows = []
            for house in houses:
                row = [house] + [current_solution[house][key] for key in ['Name', 'Smoothie', 'Cigar', 'Height', 'PhoneModel']]
                solution_rows.append(row)

            solution_dict = {
                "solution": {
                    "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                    "rows": solution_rows
                }
            }

            # Output the solution as JSON
            print(json.dumps(solution_dict, indent=2))
            return

# Solve the puzzle
solve_puzzle()