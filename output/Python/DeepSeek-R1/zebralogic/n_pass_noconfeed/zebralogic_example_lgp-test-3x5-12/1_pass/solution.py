import itertools
import json

def main():
    names = ['Eric', 'Peter', 'Arnold']
    cigars = ['blue master', 'prince', 'pall mall']
    hobbies = ['photography', 'gardening', 'cooking']
    educations = ['high school', 'associate', 'bachelor']
    drinks = ['tea', 'milk', 'water']
    
    # Generate all permutations for each attribute
    name_perms = list(itertools.permutations(names))
    cigar_perms = list(itertools.permutations(cigars))
    hobby_perms = list(itertools.permutations(hobbies))
    education_perms = list(itertools.permutations(educations))
    drink_perms = list(itertools.permutations(drinks))
    
    # Iterate through all combinations of attribute permutations
    for name_assign in name_perms:
        for cigar_assign in cigar_perms:
            for hobby_assign in hobby_perms:
                for education_assign in education_perms:
                    for drink_assign in drink_perms:
                        # Create assignment for each house
                        houses = []
                        for i in range(3):
                            house = {
                                'House': str(i+1),
                                'Name': name_assign[i],
                                'Cigar': cigar_assign[i],
                                'Hobby': hobby_assign[i],
                                'Education': education_assign[i],
                                'Drink': drink_assign[i]
                            }
                            houses.append(house)
                        
                        # Check constraints
                        valid = True
                        
                        # Constraint 1: Pall Mall smoker is Peter
                        for house in houses:
                            if house['Cigar'] == 'pall mall' and house['Name'] != 'Peter':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Constraint 2: Milk drinker directly left of high school diploma
                        milk_index = None
                        hs_index = None
                        for i, house in enumerate(houses):
                            if house['Drink'] == 'milk':
                                milk_index = i
                            if house['Education'] == 'high school':
                                hs_index = i
                        if milk_index is None or hs_index is None or milk_index + 1 != hs_index:
                            valid = False
                        if not valid:
                            continue
                            
                        # Constraint 3: Eric is tea drinker
                        for house in houses:
                            if house['Name'] == 'Eric' and house['Drink'] != 'tea':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Constraint 4: Arnold and Prince smoker adjacent
                        arnold_index = None
                        prince_index = None
                        for i, house in enumerate(houses):
                            if house['Name'] == 'Arnold':
                                arnold_index = i
                            if house['Cigar'] == 'prince':
                                prince_index = i
                        if abs(arnold_index - prince_index) != 1:
                            valid = False
                        if not valid:
                            continue
                            
                        # Constraint 5: Gardener left of Prince smoker
                        gardening_index = None
                        prince_index = None
                        for i, house in enumerate(houses):
                            if house['Hobby'] == 'gardening':
                                gardening_index = i
                            if house['Cigar'] == 'prince':
                                prince_index = i
                        if gardening_index is None or prince_index is None or gardening_index >= prince_index:
                            valid = False
                        if not valid:
                            continue
                            
                        # Constraint 6: Milk drinker has associate degree
                        for house in houses:
                            if house['Drink'] == 'milk' and house['Education'] != 'associate':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # Constraint 7: Bachelor directly left of photographer
                        bachelor_index = None
                        photo_index = None
                        for i, house in enumerate(houses):
                            if house['Education'] == 'bachelor':
                                bachelor_index = i
                            if house['Hobby'] == 'photography':
                                photo_index = i
                        if bachelor_index is None or photo_index is None or bachelor_index + 1 != photo_index:
                            valid = False
                        if not valid:
                            continue
                            
                        # If all constraints passed, format solution
                        if valid:
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                                    "rows": []
                                }
                            }
                            for house in houses:
                                row = [
                                    house['House'],
                                    house['Name'],
                                    house['Cigar'],
                                    house['Hobby'],
                                    house['Education'],
                                    house['Drink']
                                ]
                                solution['solution']['rows'].append(row)
                            
                            print(json.dumps(solution, indent=2))
                            return
    
    print("No solution found")

if __name__ == "__main__":
    main()