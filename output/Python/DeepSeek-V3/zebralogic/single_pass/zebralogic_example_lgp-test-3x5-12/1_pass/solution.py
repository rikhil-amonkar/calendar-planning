import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3']
    names = ['Eric', 'Peter', 'Arnold']
    cigars = ['blue master', 'prince', 'pall mall']  # Note: 'prince' is misspelled as 'prince' in the input, but corrected here
    hobbies = ['photography', 'gardening', 'cooking']
    educations = ['high school', 'associate', 'bachelor']
    drinks = ['tea', 'milk', 'water']
    
    # Correct cigar name from input (assuming 'prince' was intended)
    cigars = ['blue master', 'prince', 'pall mall']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for cigar_perm in permutations(cigars):
            for hobby_perm in permutations(hobbies):
                for education_perm in permutations(educations):
                    for drink_perm in permutations(drinks):
                        # Create a dictionary to hold the current assignment
                        assignment = {
                            '1': {'Name': None, 'Cigar': None, 'Hobby': None, 'Education': None, 'Drink': None},
                            '2': {'Name': None, 'Cigar': None, 'Hobby': None, 'Education': None, 'Drink': None},
                            '3': {'Name': None, 'Cigar': None, 'Hobby': None, 'Education': None, 'Drink': None}
                        }
                        
                        # Assign values to each house
                        for i in range(3):
                            house = houses[i]
                            assignment[house]['Name'] = name_perm[i]
                            assignment[house]['Cigar'] = cigar_perm[i]
                            assignment[house]['Hobby'] = hobby_perm[i]
                            assignment[house]['Education'] = education_perm[i]
                            assignment[house]['Drink'] = drink_perm[i]
                        
                        # Check constraints
                        # Constraint 1: The person partial to Pall Mall is Peter.
                        pall_mall_house = None
                        for house in houses:
                            if assignment[house]['Cigar'] == 'pall mall' and assignment[house]['Name'] != 'Peter':
                                break
                            if assignment[house]['Cigar'] == 'pall mall':
                                pall_mall_house = house
                        else:
                            if pall_mall_house is None:
                                continue  # No house has pall mall
                            
                            # Constraint 3: Eric is the tea drinker.
                            eric_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Eric' and assignment[house]['Drink'] != 'tea':
                                    break
                                if assignment[house]['Name'] == 'Eric':
                                    eric_house = house
                            else:
                                if eric_house is None:
                                    continue  # Eric not found
                                
                                # Constraint 4: Arnold and the Prince smoker are next to each other.
                                arnold_house = None
                                prince_house = None
                                for house in houses:
                                    if assignment[house]['Name'] == 'Arnold':
                                        arnold_house = house
                                    if assignment[house]['Cigar'] == 'prince':
                                        prince_house = house
                                if arnold_house is None or prince_house is None:
                                    continue
                                if abs(int(arnold_house) - int(prince_house)) != 1:
                                    continue
                                
                                # Constraint 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
                                gardening_house = None
                                for house in houses:
                                    if assignment[house]['Hobby'] == 'gardening':
                                        gardening_house = house
                                        break
                                if gardening_house is None or int(gardening_house) >= int(prince_house):
                                    continue
                                
                                # Constraint 2: The person who likes milk is directly left of the person with a high school diploma.
                                milk_house = None
                                high_school_house = None
                                for house in houses:
                                    if assignment[house]['Drink'] == 'milk':
                                        milk_house = house
                                    if assignment[house]['Education'] == 'high school':
                                        high_school_house = house
                                if milk_house is None or high_school_house is None:
                                    continue
                                if int(milk_house) + 1 != int(high_school_house):
                                    continue
                                
                                # Constraint 6: The person who likes milk is the person with an associate's degree.
                                if assignment[milk_house]['Education'] != 'associate':
                                    continue
                                
                                # Constraint 7: The person with a bachelor's degree is directly left of the photography enthusiast.
                                bachelor_house = None
                                photography_house = None
                                for house in houses:
                                    if assignment[house]['Education'] == 'bachelor':
                                        bachelor_house = house
                                    if assignment[house]['Hobby'] == 'photography':
                                        photography_house = house
                                if bachelor_house is None or photography_house is None:
                                    continue
                                if int(bachelor_house) + 1 != int(photography_house):
                                    continue
                                
                                # All constraints satisfied, prepare the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                                        "rows": []
                                    }
                                }
                                for house in houses:
                                    row = [
                                        house,
                                        assignment[house]['Name'],
                                        assignment[house]['Cigar'],
                                        assignment[house]['Hobby'],
                                        assignment[house]['Education'],
                                        assignment[house]['Drink']
                                    ]
                                    solution["solution"]["rows"].append(row)
                                return solution
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))