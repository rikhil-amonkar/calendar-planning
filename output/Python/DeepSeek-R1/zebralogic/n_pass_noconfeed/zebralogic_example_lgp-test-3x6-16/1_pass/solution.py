import itertools
import json

def main():
    # Define the attributes and their possible values
    attributes = {
        'Name': ['Eric', 'Peter', 'Arnold'],
        'Drink': ['tea', 'water', 'milk'],
        'Nationality': ['dane', 'brit', 'swede'],
        'Education': ['high school', 'associate', 'bachelor'],
        'HouseStyle': ['victorian', 'colonial', 'ranch'],
        'Smoothie': ['cherry', 'watermelon', 'desert']
    }
    
    # Generate all permutations for each attribute
    perms_list = [list(itertools.permutations(values)) for values in attributes.values()]
    
    # Iterate over the product of all attribute permutations
    for name_perm, drink_perm, nation_perm, education_perm, style_perm, smoothie_perm in itertools.product(*perms_list):
        assignment = {
            'Name': name_perm,
            'Drink': drink_perm,
            'Nationality': nation_perm,
            'Education': education_perm,
            'HouseStyle': style_perm,
            'Smoothie': smoothie_perm
        }
        
        # Check all constraints
        if check_constraints(assignment):
            # Format the solution as required
            rows = []
            for i in range(3):
                house_num = str(i+1)
                row = [house_num, 
                       assignment['Name'][i],
                       assignment['Drink'][i],
                       assignment['Nationality'][i],
                       assignment['Education'][i],
                       assignment['HouseStyle'][i],
                       assignment['Smoothie'][i]]
                rows.append(row)
            
            solution_dict = {
                "solution": {
                    "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                    "rows": rows
                }
            }
            print(json.dumps(solution_dict, indent=2))
            return

def check_constraints(ass):
    # Constraint 1: One house between Eric and tea drinker
    eric_index = ass['Name'].index('Eric')
    tea_index = ass['Drink'].index('tea')
    if abs(eric_index - tea_index) != 2:
        return False

    # Constraint 2: Milk drinker is in ranch-style home
    milk_index = ass['Drink'].index('milk')
    ranch_index = ass['HouseStyle'].index('ranch')
    if milk_index != ranch_index:
        return False

    # Constraint 3: Bachelor degree in second house
    if ass['Education'][1] != 'bachelor':
        return False

    # Constraint 4: High school diploma is Dane
    hs_index = ass['Education'].index('high school')
    dane_index = ass['Nationality'].index('dane')
    if hs_index != dane_index:
        return False

    # Constraint 5: Desert smoothie lover is Swedish
    desert_index = ass['Smoothie'].index('desert')
    swede_index = ass['Nationality'].index('swede')
    if desert_index != swede_index:
        return False

    # Constraint 6: Victorian house not in first house
    victorian_index = ass['HouseStyle'].index('victorian')
    if victorian_index == 0:
        return False

    # Constraint 7: Cherry smoothie lover is in colonial house
    cherry_index = ass['Smoothie'].index('cherry')
    colonial_index = ass['HouseStyle'].index('colonial')
    if cherry_index != colonial_index:
        return False

    # Constraint 8: Arnold is right of Victorian house
    arnold_index = ass['Name'].index('Arnold')
    if arnold_index <= victorian_index:
        return False

    # Constraint 9: Ranch-style home has high school diploma
    if ranch_index != hs_index:
        return False

    return True

if __name__ == '__main__':
    main()