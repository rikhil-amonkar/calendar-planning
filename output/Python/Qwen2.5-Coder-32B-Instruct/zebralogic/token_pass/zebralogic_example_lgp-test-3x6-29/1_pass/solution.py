import json

def is_consistent(assignment, constraints):
    for constraint in constraints:
        if not constraint(assignment):
            return False
    return True

def backtrack(assignment, unassigned_vars, constraints):
    if not unassigned_vars:
        return assignment
    
    var = unassigned_vars[0]
    remaining_vars = unassigned_vars[1:]
    
    for value in domains[var]:
        assignment[var] = value
        if is_consistent(assignment, constraints):
            result = backtrack(assignment, remaining_vars, constraints)
            if result is not None:
                return result
        del assignment[var]
    return None

# Define variables and domains
houses = ['house1', 'house2', 'house3']
people = ['Arnold', 'Peter', 'Eric']
animals = ['bird', 'horse', 'cat']
birthdays = ['jan', 'sept', 'april']
hobbies = ['photography', 'cooking', 'gardening']
drinks = ['milk', 'water', 'tea']
hair_colors = ['black', 'brown', 'blonde']

domains = {}
for house in houses:
    domains[f'{house}_name'] = people.copy()
    domains[f'{house}_animal'] = animals.copy()
    domains[f'{house}_birthday'] = birthdays.copy()
    domains[f'{house}_hobby'] = hobbies.copy()
    domains[f'{house}_drink'] = drinks.copy()
    domains[f'{house}_hair_color'] = hair_colors.copy()

# Define constraints
constraints = [
    lambda a: a.get('house1_hair_color') != 'brown' or a.get('house1_hobby') == 'cooking',
    lambda a: a.get('house3_birthday') == 'april',
    lambda a: a.get('house1_name') != 'Eric',
    lambda a: a.get('house2_animal') == 'cat',
    lambda a: (a.get('house1_hair_color') == 'blonde' and a.get('house2_drink') != 'milk') or 
               (a.get('house2_hair_color') == 'blonde' and a.get('house3_drink') != 'milk'),
    lambda a: a.get('house1_hobby') != 'gardening' or a.get('house1_drink') == 'milk',
    lambda a: a.get('house2_hair_color') == 'brown' and a.get('house2_animal') == 'cat',
    lambda a: a.get('house1_name') == 'Arnold' and a.get('house1_animal') == 'bird',
    lambda a: a.get('house1_drink') != 'water' or a.get('house1_hobby') == 'photography',
    lambda a: a.get('house2_name') != 'Arnold' or a.get('house1_birthday') == 'sept'
]

# Solve the puzzle
unassigned_vars = list(domains.keys())
assignment = backtrack({}, unassigned_vars, constraints)

# Format the solution
solution = {
    "solution": {
        "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
        "rows": []
    }
}

for i, house in enumerate(houses):
    row = [
        str(i + 1),
        assignment[f'{house}_name'],
        assignment[f'{house}_animal'],
        assignment[f'{house}_birthday'],
        assignment[f'{house}_hobby'],
        assignment[f'{house}_drink'],
        assignment[f'{house}_hair_color']
    ]
    solution["solution"]["rows"].append(row)

print(json.dumps(solution, indent=2))