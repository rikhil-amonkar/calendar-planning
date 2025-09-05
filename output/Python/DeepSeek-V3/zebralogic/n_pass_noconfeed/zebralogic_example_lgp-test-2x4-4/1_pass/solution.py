import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    educations = ['associate', 'high school']
    
    # Generate all possible permutations for each attribute
    name_perms = list(permutations(names))
    style_perms = list(permutations(house_styles))
    height_perms = list(permutations(heights))
    education_perms = list(permutations(educations))
    
    # Try all possible combinations
    for name_assignment in name_perms:
        for style_assignment in style_perms:
            for height_assignment in height_perms:
                for education_assignment in education_perms:
                    # Create house assignments
                    houses = [
                        {
                            'House': '1',
                            'Name': name_assignment[0],
                            'HouseStyle': style_assignment[0],
                            'Height': height_assignment[0],
                            'Education': education_assignment[0]
                        },
                        {
                            'House': '2',
                            'Name': name_assignment[1],
                            'HouseStyle': style_assignment[1],
                            'Height': height_assignment[1],
                            'Education': education_assignment[1]
                        }
                    ]
                    
                    # Check clue 1: The person who is short is directly left of Eric
                    short_person_left_of_eric = False
                    for i in range(2):
                        if houses[i]['Height'] == 'short':
                            # Check if Eric is in the next house (right)
                            if i == 0 and houses[1]['Name'] == 'Eric':
                                short_person_left_of_eric = True
                            break
                    
                    # Check clue 2: The person residing in a Victorian house is in the first house
                    victorian_in_first = houses[0]['HouseStyle'] == 'victorian'
                    
                    # Check clue 3: The person who is short is the person with an associate's degree
                    short_has_associate = False
                    for house in houses:
                        if house['Height'] == 'short' and house['Education'] == 'associate':
                            short_has_associate = True
                            break
                    
                    # If all clues are satisfied, return the solution
                    if short_person_left_of_eric and victorian_in_first and short_has_associate:
                        return houses
    
    return None

def main():
    solution = solve_puzzle()
    
    if solution:
        # Format the solution as required
        header = ["House", "Name", "HouseStyle", "Height", "Education"]
        rows = []
        
        for house in solution:
            row = [
                house['House'],
                house['Name'],
                house['HouseStyle'],
                house['Height'],
                house['Education']
            ]
            rows.append(row)
        
        # Create the output dictionary
        output = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        # Output as JSON
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()