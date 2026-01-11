import itertools
import json

# Define the attributes
names = ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice']
house_styles = ['modern', 'craftsman', 'ranch', 'victorian', 'colonial']
mothers_names = ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya']
phone_models = ['oneplus 9', 'google pixel 6', 'huawei p50', 'iphone 13', 'samsung galaxy s21']
drinks = ['coffee', 'water', 'root beer', 'tea', 'milk']
animals = ['fish', 'dog', 'horse', 'bird', 'cat']

# Define the constraints
def is_valid_solution(solution):
    # Unpack the solution into separate lists
    names_sol, house_styles_sol, mothers_names_sol, phone_models_sol, drinks_sol, animals_sol = zip(*solution)
    
    # Check each constraint
    if phone_models_sol.index('google pixel 6') == 0:
        return False
    if drinks_sol[names_sol.index('Alice')] != 'water':
        return False
    if house_styles_sol.index('colonial') < phone_models_sol.index('huawei p50'):
        return False
    if animals_sol.index('horse') != phone_models_sol.index('oneplus 9'):
        return False
    if house_styles_sol.index('ranch') != mothers_names_sol.index('Kailyn'):
        return False
    if drinks_sol.index('root beer') != animals_sol.index('cat'):
        return False
    if house_styles_sol.index('colonial') == 3:
        return False
    if animals_sol[3] != 'bird':
        return False
    if drinks_sol[names_sol.index('Bob')] != 'tea':
        return False
    if drinks_sol.index('tea') < mothers_names_sol.index('Kailyn'):
        return False
    if drinks_sol.index('root beer') > mothers_names_sol.index('Kailyn'):
        return False
    if animals_sol.index('horse') != house_styles_sol.index('modern'):
        return False
    if phone_models_sol.index('iphone 13') != drinks_sol.index('milk'):
        return False
    if animals_sol.index('dog') != drinks_sol.index('milk'):
        return False
    if phone_models_sol.index('google pixel 6') != house_styles_sol.index('craftsman'):
        return False
    if names_sol[1] == 'Eric':
        return False
    if drinks_sol[3] != 'tea':
        return False
    if animals_sol.index('horse') != 2:
        return False
    if house_styles_sol.index('modern') != mothers_names_sol.index('Penny'):
        return False
    if names_sol[drinks_sol.index('root beer')] != 'Peter':
        return False
    if mothers_names_sol[3] == 'Aniya':
        return False
    if mothers_names_sol.index('Janelle') != drinks_sol.index('water'):
        return False
    
    return True

# Generate all permutations for each category
all_permutations = list(itertools.permutations(range(5)))

# Try all combinations
for names_perm in all_permutations:
    for house_styles_perm in all_permutations:
        for mothers_names_perm in all_permutations:
            for phone_models_perm in all_permutations:
                for drinks_perm in all_permutations:
                    for animals_perm in all_permutations:
                        solution = list(zip(names_perm, house_styles_perm, mothers_names_perm, phone_models_perm, drinks_perm, animals_perm))
                        if is_valid_solution(solution):
                            # Convert indices to actual values
                            final_solution = []
                            for i in range(5):
                                final_solution.append([
                                    str(i + 1),
                                    names[solution[i][0]],
                                    house_styles[solution[i][1]],
                                    mothers_names[solution[i][2]],
                                    phone_models[solution[i][3]],
                                    drinks[solution[i][4]],
                                    animals[solution[i][5]]
                                ])
                            
                            # Output the solution as JSON
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                                    "rows": final_solution
                                }
                            }
                            print(json.dumps(result, indent=2))
                            exit()