import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Arnold', 'Peter', 'Eric', 'Alice']
    house_styles = ['craftsman', 'colonial', 'victorian', 'ranch']
    hair_colors = ['red', 'blonde', 'black', 'brown']
    children = ['Bella', 'Fred', 'Meredith', 'Samantha']
    book_genres = ['mystery', 'fantasy', 'romance', 'science fiction']
    
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            for hair_perm in permutations(hair_colors):
                for child_perm in permutations(children):
                    for book_perm in permutations(book_genres):
                        
                        # Create assignment dictionaries for each house
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                'Name': name_perm[i],
                                'HouseStyle': style_perm[i],
                                'HairColor': hair_perm[i],
                                'Children': child_perm[i],
                                'BookGenre': book_perm[i]
                            }
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: Craftsman-style house is in the third house
                        if assignment[3]['HouseStyle'] != 'craftsman':
                            valid = False
                            continue
                        
                        # Clue 2: Alice loves romance books
                        for house in houses:
                            if assignment[house]['Name'] == 'Alice' and assignment[house]['BookGenre'] != 'romance':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 3: Brown hair in fourth house
                        if assignment[4]['HairColor'] != 'brown':
                            valid = False
                            continue
                        
                        # Clue 4: Child Samantha in fourth house
                        if assignment[4]['Children'] != 'Samantha':
                            valid = False
                            continue
                        
                        # Clue 5: Ranch-style home is to the right of red hair
                        red_hair_house = None
                        ranch_house = None
                        for house in houses:
                            if assignment[house]['HairColor'] == 'red':
                                red_hair_house = house
                            if assignment[house]['HouseStyle'] == 'ranch':
                                ranch_house = house
                        if red_hair_house is None or ranch_house is None or ranch_house <= red_hair_house:
                            valid = False
                            continue
                        
                        # Clue 6: Peter has child Bella
                        for house in houses:
                            if assignment[house]['Name'] == 'Peter' and assignment[house]['Children'] != 'Bella':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 7: Arnold has red hair
                        for house in houses:
                            if assignment[house]['Name'] == 'Arnold' and assignment[house]['HairColor'] != 'red':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 8: Alice lives in colonial-style house
                        for house in houses:
                            if assignment[house]['Name'] == 'Alice' and assignment[house]['HouseStyle'] != 'colonial':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 9: Black hair in second house
                        if assignment[2]['HairColor'] != 'black':
                            valid = False
                            continue
                        
                        # Clue 10: Peter loves fantasy books
                        for house in houses:
                            if assignment[house]['Name'] == 'Peter' and assignment[house]['BookGenre'] != 'fantasy':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 11: Arnold has child Meredith
                        for house in houses:
                            if assignment[house]['Name'] == 'Arnold' and assignment[house]['Children'] != 'Meredith':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 12: Eric has black hair
                        for house in houses:
                            if assignment[house]['Name'] == 'Eric' and assignment[house]['HairColor'] != 'black':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # Clue 13: Arnold loves science fiction books
                        for house in houses:
                            if assignment[house]['Name'] == 'Arnold' and assignment[house]['BookGenre'] != 'science fiction':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # If we reach here, all constraints are satisfied
                        if valid:
                            # Format the solution
                            rows = []
                            for house in sorted(assignment.keys()):
                                row = [
                                    str(house),
                                    assignment[house]['Name'],
                                    assignment[house]['HouseStyle'],
                                    assignment[house]['HairColor'],
                                    assignment[house]['Children'],
                                    assignment[house]['BookGenre']
                                ]
                                rows.append(row)
                            
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                                    "rows": rows
                                }
                            }
                            return result
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()