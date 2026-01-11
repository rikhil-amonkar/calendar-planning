import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    houses = [1, 2, 3]
    names = ["Peter", "Arnold", "Eric"]
    genres = ["science fiction", "mystery", "romance"]
    smoothies = ["watermelon", "desert", "cherry"]
    birthdays = ["april", "jan", "sept"]
    heights = ["average", "very short", "short"]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names, 3):
        for genre_perm in permutations(genres, 3):
            for smoothie_perm in permutations(smoothies, 3):
                for birthday_perm in permutations(birthdays, 3):
                    for height_perm in permutations(heights, 3):
                        # Create assignment: house index -> attributes
                        assignment = {}
                        for i in range(3):
                            assignment[i+1] = {
                                "Name": name_perm[i],
                                "BookGenre": genre_perm[i],
                                "Smoothie": smoothie_perm[i],
                                "Birthday": birthday_perm[i],
                                "Height": height_perm[i]
                            }
                        
                        # Check all clues
                        # 1. Cherry smoothie not in second house
                        if assignment[2]["Smoothie"] == "cherry":
                            continue
                        
                        # 2. Arnold loves mystery books
                        arnold_house = None
                        for house, attrs in assignment.items():
                            if attrs["Name"] == "Arnold":
                                arnold_house = house
                                break
                        if arnold_house is None:
                            continue
                        if assignment[arnold_house]["BookGenre"] != "mystery":
                            continue
                        
                        # 3. January birthday not in first house
                        if assignment[1]["Birthday"] == "jan":
                            continue
                        
                        # 4. Very short person loves romance books
                        very_short_house = None
                        for house, attrs in assignment.items():
                            if attrs["Height"] == "very short":
                                very_short_house = house
                                break
                        if very_short_house is None:
                            continue
                        if assignment[very_short_house]["BookGenre"] != "romance":
                            continue
                        
                        # 5. Mystery book lover has September birthday
                        mystery_house = None
                        for house, attrs in assignment.items():
                            if attrs["BookGenre"] == "mystery":
                                mystery_house = house
                                break
                        if mystery_house is None:
                            continue
                        if assignment[mystery_house]["Birthday"] != "sept":
                            continue
                        
                        # 6. Average height person loves Desert smoothie
                        avg_height_house = None
                        for house, attrs in assignment.items():
                            if attrs["Height"] == "average":
                                avg_height_house = house
                                break
                        if avg_height_house is None:
                            continue
                        if assignment[avg_height_house]["Smoothie"] != "desert":
                            continue
                        
                        # 7. Eric is in first house
                        if assignment[1]["Name"] != "Eric":
                            continue
                        
                        # 8. Watermelon smoothie lover is short
                        watermelon_house = None
                        for house, attrs in assignment.items():
                            if attrs["Smoothie"] == "watermelon":
                                watermelon_house = house
                                break
                        if watermelon_house is None:
                            continue
                        if assignment[watermelon_house]["Height"] != "short":
                            continue
                        
                        # 9. Watermelon smoothie lover is Eric
                        if assignment[watermelon_house]["Name"] != "Eric":
                            continue
                        
                        # All constraints satisfied - found solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                                "rows": []
                            }
                        }
                        
                        for house in sorted(assignment.keys()):
                            attrs = assignment[house]
                            row = [
                                str(house),
                                attrs["Name"],
                                attrs["BookGenre"],
                                attrs["Smoothie"],
                                attrs["Birthday"],
                                attrs["Height"]
                            ]
                            solution["solution"]["rows"].append(row)
                        
                        return solution
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()