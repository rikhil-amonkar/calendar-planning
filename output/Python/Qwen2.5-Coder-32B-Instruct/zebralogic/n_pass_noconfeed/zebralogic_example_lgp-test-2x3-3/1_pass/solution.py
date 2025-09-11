import json

def solve_puzzle():
    # Define possible values for each characteristic
    houses = ['1', '2']
    names = ['Arnold', 'Eric']
    foods = ['grilled cheese', 'pizza']
    mothers = ['Holly', 'Aniya']

    # Initialize the solution space
    solutions = []

    # Generate all possible permutations
    for h1_name in names:
        for h1_food in foods:
            for h1_mother in mothers:
                remaining_names = [name for name in names if name != h1_name]
                remaining_foods = [food for food in foods if food != h1_food]
                remaining_mothers = [mother for mother in mothers if mother != h1_mother]

                for h2_name in remaining_names:
                    for h2_food in remaining_foods:
                        for h2_mother in remaining_mothers:
                            # Create a potential solution
                            house1 = {'Name': h1_name, 'Food': h1_food, 'Mother': h1_mother}
                            house2 = {'Name': h2_name, 'Food': h2_food, 'Mother': h2_mother}
                            
                            # Check constraints
                            if (house1['Food'] == 'grilled cheese' and house2['Food'] == 'pizza') and \
                               (house1['Name'] != 'Eric') and \
                               (house1['Mother'] == 'Holly'):
                                solutions.append([house1, house2])

    # Format the solution as required
    if solutions:
        formatted_solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Mother"],
                "rows": [
                    ["1", solutions[0][0]['Name'], solutions[0][0]['Food'], solutions[0][0]['Mother']],
                    ["2", solutions[0][1]['Name'], solutions[0][1]['Food'], solutions[0][1]['Mother']]
                ]
            }
        }
        return json.dumps(formatted_solution, indent=2)
    else:
        return json.dumps({"solution": {"header": [], "rows": []}})

# Run the solver and print the result
print(solve_puzzle())