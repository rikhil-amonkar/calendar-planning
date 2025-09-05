import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold', 'Alice']
    smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
    cigars = ['blue master', 'pall mall', 'dunhill', 'prince']
    heights = ['tall', 'average', 'short', 'very short']
    phones = ['google pixel 6', 'samsung galaxy s21', 'iphone 13', 'oneplus 9']
    
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for smoothie_perm in permutations(smoothies):
            for cigar_perm in permutations(cigars):
                for height_perm in permutations(heights):
                    for phone_perm in permutations(phones):
                        # Create assignment dictionaries for each house
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                'name': name_perm[i],
                                'smoothie': smoothie_perm[i],
                                'cigar': cigar_perm[i],
                                'height': height_perm[i],
                                'phone': phone_perm[i]
                            }
                        
                        # Check all constraints
                        # 1. The Dragonfruit smoothie lover is Eric.
                        valid = True
                        for house in houses:
                            if assignment[house]['smoothie'] == 'dragonfruit' and assignment[house]['name'] != 'Eric':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # 2. The Dunhill smoker is the person who likes Cherry smoothies.
                        for house in houses:
                            if assignment[house]['cigar'] == 'dunhill' and assignment[house]['smoothie'] != 'cherry':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # 3. The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
                        samsung_house = None
                        iphone_house = None
                        for house in houses:
                            if assignment[house]['phone'] == 'samsung galaxy s21':
                                samsung_house = house
                            if assignment[house]['phone'] == 'iphone 13':
                                iphone_house = house
                        if samsung_house is None or iphone_house is None or samsung_house + 1 != iphone_house:
                            valid = False
                        if not valid:
                            continue
                            
                        # 4. The Dunhill smoker is somewhere to the right of the person who is very short.
                        dunhill_house = None
                        very_short_house = None
                        for house in houses:
                            if assignment[house]['cigar'] == 'dunhill':
                                dunhill_house = house
                            if assignment[house]['height'] == 'very short':
                                very_short_house = house
                        if dunhill_house is None or very_short_house is None or dunhill_house <= very_short_house:
                            valid = False
                        if not valid:
                            continue
                            
                        # 5. The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
                        watermelon_house = None
                        desert_house = None
                        for house in houses:
                            if assignment[house]['smoothie'] == 'watermelon':
                                watermelon_house = house
                            if assignment[house]['smoothie'] == 'desert':
                                desert_house = house
                        if watermelon_house is None or desert_house is None or watermelon_house <= desert_house:
                            valid = False
                        if not valid:
                            continue
                            
                        # 6. The Prince smoker is the person who uses a OnePlus 9.
                        for house in houses:
                            if assignment[house]['cigar'] == 'prince' and assignment[house]['phone'] != 'oneplus 9':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # 7. The person who is tall is in the third house.
                        if assignment[3]['height'] != 'tall':
                            valid = False
                        if not valid:
                            continue
                            
                        # 8. The person who is very short is the person who uses an iPhone 13.
                        for house in houses:
                            if assignment[house]['height'] == 'very short' and assignment[house]['phone'] != 'iphone 13':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # 9. The person who smokes Blue Master is not in the first house.
                        if assignment[1]['cigar'] == 'blue master':
                            valid = False
                        if not valid:
                            continue
                            
                        # 10. The Dunhill smoker is the person who is short.
                        for house in houses:
                            if assignment[house]['cigar'] == 'dunhill' and assignment[house]['height'] != 'short':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # 11. Peter is not in the third house.
                        if assignment[3]['name'] == 'Peter':
                            valid = False
                        if not valid:
                            continue
                            
                        # 12. Arnold is the person who uses a Google Pixel 6.
                        for house in houses:
                            if assignment[house]['name'] == 'Arnold' and assignment[house]['phone'] != 'google pixel 6':
                                valid = False
                                break
                        if not valid:
                            continue
                            
                        # 13. The Dragonfruit smoothie lover is the person partial to Pall Mall.
                        for house in houses:
                            if assignment[house]['smoothie'] == 'dragonfruit' and assignment[house]['cigar'] != 'pall mall':
                                valid = False
                                break
                        if not valid:
                            continue
                        
                        # If we get here, all constraints are satisfied
                        # Format the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                                "rows": []
                            }
                        }
                        
                        for house in houses:
                            row = [
                                str(house),
                                assignment[house]['name'],
                                assignment[house]['smoothie'],
                                assignment[house]['cigar'],
                                assignment[house]['height'],
                                assignment[house]['phone']
                            ]
                            solution["solution"]["rows"].append(row)
                        
                        # Output the solution as JSON
                        print(json.dumps(solution, indent=2))
                        return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()