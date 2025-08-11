import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4']
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for cigar_perm in permutations(cigars):
                for height_perm in permutations(heights):
                    for phone_perm in permutations(phones):
                        # Create a dictionary to hold the current assignment
                        assignment = {
                            '1': {},
                            '2': {},
                            '3': {},
                            '4': {}
                        }
                        for i in range(4):
                            house = houses[i]
                            assignment[house]['Name'] = name_perm[i]
                            assignment[house]['Smoothie'] = smoothie_perm[i]
                            assignment[house]['Cigar'] = cigar_perm[i]
                            assignment[house]['Height'] = height_perm[i]
                            assignment[house]['Phone'] = phone_perm[i]
                        
                        # Check all constraints
                        # 1. The Dragonfruit smoothie lover is Eric.
                        valid = True
                        for house in assignment:
                            if assignment[house]['Smoothie'] == 'dragonfruit' and assignment[house]['Name'] != 'Eric':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # 2. The Dunhill smoker is the person who likes Cherry smoothies.
                        for house in assignment:
                            if assignment[house]['Cigar'] == 'dunhill' and assignment[house]['Smoothie'] != 'cherry':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # 3. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
                        found = False
                        for i in range(3):
                            if assignment[houses[i]]['Phone'] == 'samsung galaxy s21' and assignment[houses[i+1]]['Phone'] == 'iphone 13':
                                found = True
                                break
                        if not found:
                            valid = False
                        if not valid:
                            continue
                        
                        # 4. The Dunhill smoker is somewhere to the right of the person who is very short.
                        very_short_house = None
                        dunhill_house = None
                        for house in assignment:
                            if assignment[house]['Height'] == 'very short':
                                very_short_house = int(house)
                            if assignment[house]['Cigar'] == 'dunhill':
                                dunhill_house = int(house)
                        if very_short_house is None or dunhill_house is None or dunhill_house <= very_short_house:
                            valid = False
                        if not valid:
                            continue
                        
                        # 5. The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
                        desert_house = None
                        watermelon_house = None
                        for house in assignment:
                            if assignment[house]['Smoothie'] == 'desert':
                                desert_house = int(house)
                            if assignment[house]['Smoothie'] == 'watermelon':
                                watermelon_house = int(house)
                        if desert_house is None or watermelon_house is None or watermelon_house <= desert_house:
                            valid = False
                        if not valid:
                            continue
                        
                        # 6. The Prince smoker is the person who uses a OnePlus 9.
                        for house in assignment:
                            if assignment[house]['Cigar'] == 'prince' and assignment[house]['Phone'] != 'oneplus 9':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # 7. The person who is tall is in the third house.
                        if assignment['3']['Height'] != 'tall':
                            valid = False
                        if not valid:
                            continue
                        
                        # 8. The person who is very short is the person who uses an iPhone 13.
                        for house in assignment:
                            if assignment[house]['Height'] == 'very short' and assignment[house]['Phone'] != 'iphone 13':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # 9. The person who smokes Blue Master is not in the first house.
                        if assignment['1']['Cigar'] == 'blue master':
                            valid = False
                        if not valid:
                            continue
                        
                        # 10. The Dunhill smoker is the person who is short.
                        for house in assignment:
                            if assignment[house]['Cigar'] == 'dunhill' and assignment[house]['Height'] != 'short':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # 11. Peter is not in the third house.
                        if assignment['3']['Name'] == 'Peter':
                            valid = False
                        if not valid:
                            continue
                        
                        # 12. Arnold is the person who uses a Google Pixel 6.
                        for house in assignment:
                            if assignment[house]['Name'] == 'Arnold' and assignment[house]['Phone'] != 'google pixel 6':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # 13. The Dragonfruit smoothie lover is the person partial to Pall Mall.
                        for house in assignment:
                            if assignment[house]['Smoothie'] == 'dragonfruit' and assignment[house]['Cigar'] != 'pall mall':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # If all constraints are satisfied, return the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "Phone"],
                                "rows": []
                            }
                        }
                        for house in houses:
                            row = [house]
                            row.append(assignment[house]['Name'])
                            row.append(assignment[house]['Smoothie'])
                            row.append(assignment[house]['Cigar'])
                            row.append(assignment[house]['Height'])
                            row.append(assignment[house]['Phone'])
                            solution["solution"]["rows"].append(row)
                        return solution
    
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))