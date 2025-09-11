import json

# Define all possible options for each category
names_options = [
    ['Arnold', 'Eric'],
    ['Eric', 'Arnold']
]

mothers_options = [
    ['Aniya', 'Holly'],
    ['Holly', 'Aniya']
]

cars_options = [
    ['ford f150', 'tesla model 3'],
    ['tesla model 3', 'ford f150']
]

heights_options = [
    ['short', 'very short'],
    ['very short', 'short']
]

solution_found = None

for names in names_options:
    for mothers in mothers_options:
        # Check clue 3: The person whose mother's name is Holly is in the second house
        if mothers[1] != 'Holly':
            continue
        for cars in cars_options:
            for heights in heights_options:
                # Check clue 2: Arnold is the person who is short
                arnold_index = names.index('Arnold')
                if heights[arnold_index] != 'short':
                    continue
                # Check clue 1: The person who owns a Tesla Model 3 is somewhere to the right of Arnold
                tesla_house = 1 if cars[0] == 'tesla model 3' else 2
                arnold_house = arnold_index + 1
                if tesla_house <= arnold_house:
                    continue
                # Construct the solution if all constraints are satisfied
                solution_rows = []
                for i in range(2):
                    house_num = str(i + 1)
                    solution_rows.append([
                        house_num,
                        names[i],
                        mothers[i],
                        cars[i],
                        heights[i]
                    ])
                solution_found = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "CarModel", "Height"],
                        "rows": solution_rows
                    }
                }
                # Exit loops once a solution is found
                break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

# Output the JSON-formatted solution
print(json.dumps(solution_found, indent=2))