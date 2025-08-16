import itertools
import json

def main():
    attributes = {
        'Name': ['Eric', 'Peter', 'Arnold'],
        'Cigar': ['blue master', 'prince', 'pall mall'],
        'Hobby': ['photography', 'gardening', 'cooking'],
        'Education': ['high school', 'associate', 'bachelor'],
        'Drink': ['tea', 'milk', 'water']
    }
    
    def satisfies_constraints(houses):
        # Constraint 1: Pall Mall smoker is Peter
        for i in range(3):
            if houses[i]['Cigar'] == 'pall mall':
                if houses[i]['Name'] != 'Peter':
                    return False
                break
        
        # Constraint 2: Milk drinker directly left of high school diploma
        milk_index = None
        for i in range(3):
            if houses[i]['Drink'] == 'milk':
                milk_index = i
        if milk_index is None or milk_index == 2:
            return False
        if houses[milk_index + 1]['Education'] != 'high school':
            return False
        
        # Constraint 3: Eric drinks tea
        for i in range(3):
            if houses[i]['Name'] == 'Eric':
                if houses[i]['Drink'] != 'tea':
                    return False
                break
        
        # Constraint 4: Arnold and Prince smoker are adjacent
        arnold_index = None
        prince_index = None
        for i in range(3):
            if houses[i]['Name'] == 'Arnold':
                arnold_index = i
            if houses[i]['Cigar'] == 'prince':
                prince_index = i
        if arnold_index is None or prince_index is None:
            return False
        if abs(arnold_index - prince_index) != 1:
            return False
        
        # Constraint 5: Gardening left of Prince smoker
        gardening_index = None
        for i in range(3):
            if houses[i]['Hobby'] == 'gardening':
                gardening_index = i
                break
        if gardening_index is None:
            return False
        if gardening_index >= prince_index:
            return False
        
        # Constraint 6: Milk drinker has associate's degree
        if houses[milk_index]['Education'] != 'associate':
            return False
        
        # Constraint 7: Bachelor directly left of photography
        bachelor_index = None
        photo_index = None
        for i in range(3):
            if houses[i]['Education'] == 'bachelor':
                bachelor_index = i
            if houses[i]['Hobby'] == 'photography':
                photo_index = i
        if bachelor_index is None or photo_index is None:
            return False
        if bachelor_index + 1 != photo_index:
            return False
        
        return True

    solution_found = False
    solution_rows = None

    for names in itertools.permutations(attributes['Name']):
        if solution_found:
            break
        for cigars in itertools.permutations(attributes['Cigar']):
            if solution_found:
                break
            for hobbies in itertools.permutations(attributes['Hobby']):
                if solution_found:
                    break
                for educations in itertools.permutations(attributes['Education']):
                    if solution_found:
                        break
                    for drinks in itertools.permutations(attributes['Drink']):
                        houses = []
                        for i in range(3):
                            house = {
                                'Name': names[i],
                                'Cigar': cigars[i],
                                'Hobby': hobbies[i],
                                'Education': educations[i],
                                'Drink': drinks[i]
                            }
                            houses.append(house)
                        
                        if satisfies_constraints(houses):
                            solution_rows = []
                            for i in range(3):
                                row = [str(i+1), houses[i]['Name'], houses[i]['Cigar'], houses[i]['Hobby'], houses[i]['Education'], houses[i]['Drink']]
                                solution_rows.append(row)
                            solution_found = True
                            break

    if solution_found:
        result = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()