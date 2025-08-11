import itertools
import json

def main():
    attributes = ['Name', 'Hobby', 'BookGenre', 'MusicGenre', 'BirthdayMonth']
    domains = {
        'Name': ['Eric', 'Arnold'],
        'Hobby': ['gardening', 'photography'],
        'BookGenre': ['science fiction', 'mystery'],
        'MusicGenre': ['rock', 'pop'],
        'BirthdayMonth': ['april', 'sept']
    }
    
    per_attr_choices = {}
    for attr in attributes:
        vals = domains[attr]
        per_attr_choices[attr] = [
            {'house1': vals[0], 'house2': vals[1]},
            {'house1': vals[1], 'house2': vals[0]}
        ]
    
    all_combinations = itertools.product(*(per_attr_choices[attr] for attr in attributes))
    
    solutions = []
    
    def check_clue1(assignment):
        house1, house2 = assignment
        if house1['BookGenre'] == 'mystery' and house1['MusicGenre'] != 'rock':
            return False
        if house2['BookGenre'] == 'mystery' and house2['MusicGenre'] != 'rock':
            return False
        return True

    def check_clue2(assignment):
        house1, house2 = assignment
        return house1['Name'] != 'Arnold'

    def check_clue3(assignment):
        house1, house2 = assignment
        if house1['BookGenre'] == 'mystery' and house1['Hobby'] != 'gardening':
            return False
        if house2['BookGenre'] == 'mystery' and house2['Hobby'] != 'gardening':
            return False
        return True

    def check_clue4(assignment):
        house1, house2 = assignment
        if house1['BirthdayMonth'] == 'april' and house1['Name'] != 'Arnold':
            return False
        if house2['BirthdayMonth'] == 'april' and house2['Name'] != 'Arnold':
            return False
        return True

    def check_clue5(assignment):
        house1, house2 = assignment
        return house1['BookGenre'] == 'mystery'
    
    constraints = [check_clue1, check_clue2, check_clue3, check_clue4, check_clue5]
    
    for comb in all_combinations:
        house1 = {}
        house2 = {}
        for idx, attr in enumerate(attributes):
            house1[attr] = comb[idx]['house1']
            house2[attr] = comb[idx]['house2']
        assignment = [house1, house2]
        
        valid = True
        for constraint in constraints:
            if not constraint(assignment):
                valid = False
                break
                
        if valid:
            solutions.append(assignment)
            
    if not solutions:
        print(json.dumps({"error": "No solution found"}))
        return
        
    sol_assignment = solutions[0]
    house1, house2 = sol_assignment
    
    header = ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "BirthdayMonth"]
    row1 = ["1", house1['Name'], house1['Hobby'], house1['BookGenre'], house1['MusicGenre'], house1['BirthdayMonth']]
    row2 = ["2", house2['Name'], house2['Hobby'], house2['BookGenre'], house2['MusicGenre'], house2['BirthdayMonth']]
    
    output = {
        "solution": {
            "header": header,
            "rows": [row1, row2]
        }
    }
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()