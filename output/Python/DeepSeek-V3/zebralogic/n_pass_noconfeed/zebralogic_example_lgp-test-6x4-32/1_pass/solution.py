import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
    house_styles = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
    music_genres = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
    hobbies = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']
    
    houses = [1, 2, 3, 4, 5, 6]
    
    # Try all possible permutations
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            for music_perm in permutations(music_genres):
                for hobby_perm in permutations(hobbies):
                    # Create assignment dictionaries
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            'name': name_perm[i],
                            'style': style_perm[i],
                            'music': music_perm[i],
                            'hobby': hobby_perm[i]
                        }
                    
                    # Check all constraints
                    valid = True
                    
                    # Clue 1: The person who loves rock music is in the fifth house.
                    if assignment[5]['music'] != 'rock':
                        valid = False
                        continue
                    
                    # Clue 2: The person who loves classical music and the woodworking hobbyist are next to each other.
                    classical_house = None
                    woodworking_house = None
                    for house in houses:
                        if assignment[house]['music'] == 'classical':
                            classical_house = house
                        if assignment[house]['hobby'] == 'woodworking':
                            woodworking_house = house
                    if classical_house is None or woodworking_house is None or abs(classical_house - woodworking_house) != 1:
                        valid = False
                        continue
                    
                    # Clue 3: The person in a Mediterranean-style villa is the person who loves hip-hop music.
                    for house in houses:
                        if assignment[house]['style'] == 'mediterranean' and assignment[house]['music'] != 'hip hop':
                            valid = False
                            break
                        if assignment[house]['music'] == 'hip hop' and assignment[house]['style'] != 'mediterranean':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 4: There are two houses between Arnold and the person residing in a Victorian house.
                    arnold_house = None
                    victorian_house = None
                    for house in houses:
                        if assignment[house]['name'] == 'Arnold':
                            arnold_house = house
                        if assignment[house]['style'] == 'victorian':
                            victorian_house = house
                    if arnold_house is None or victorian_house is None or abs(arnold_house - victorian_house) != 3:
                        valid = False
                        continue
                    
                    # Clue 5: The person who loves jazz music is directly left of Eric.
                    jazz_house = None
                    eric_house = None
                    for house in houses:
                        if assignment[house]['music'] == 'jazz':
                            jazz_house = house
                        if assignment[house]['name'] == 'Eric':
                            eric_house = house
                    if jazz_house is None or eric_house is None or jazz_house + 1 != eric_house:
                        valid = False
                        continue
                    
                    # Clue 6: The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
                    hiphop_house = None
                    knitting_house = None
                    for house in houses:
                        if assignment[house]['music'] == 'hip hop':
                            hiphop_house = house
                        if assignment[house]['hobby'] == 'knitting':
                            knitting_house = house
                    if hiphop_house is None or knitting_house is None or hiphop_house >= knitting_house:
                        valid = False
                        continue
                    
                    # Clue 7: Carol is the person who loves hip-hop music.
                    for house in houses:
                        if assignment[house]['name'] == 'Carol' and assignment[house]['music'] != 'hip hop':
                            valid = False
                            break
                        if assignment[house]['music'] == 'hip hop' and assignment[house]['name'] != 'Carol':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 8: The person in a Craftsman-style house is Arnold.
                    for house in houses:
                        if assignment[house]['style'] == 'craftsman' and assignment[house]['name'] != 'Arnold':
                            valid = False
                            break
                        if assignment[house]['name'] == 'Arnold' and assignment[house]['style'] != 'craftsman':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 9: The person in a ranch-style home is Eric.
                    for house in houses:
                        if assignment[house]['style'] == 'ranch' and assignment[house]['name'] != 'Eric':
                            valid = False
                            break
                        if assignment[house]['name'] == 'Eric' and assignment[house]['style'] != 'ranch':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 10: The woodworking hobbyist is the person residing in a Victorian house.
                    for house in houses:
                        if assignment[house]['hobby'] == 'woodworking' and assignment[house]['style'] != 'victorian':
                            valid = False
                            break
                        if assignment[house]['style'] == 'victorian' and assignment[house]['hobby'] != 'woodworking':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 11: The person who loves country music is in the first house.
                    if assignment[1]['music'] != 'country':
                        valid = False
                        continue
                    
                    # Clue 12: There is one house between the person who paints as a hobby and the person living in a colonial-style house.
                    painting_house = None
                    colonial_house = None
                    for house in houses:
                        if assignment[house]['hobby'] == 'painting':
                            painting_house = house
                        if assignment[house]['style'] == 'colonial':
                            colonial_house = house
                    if painting_house is None or colonial_house is None or abs(painting_house - colonial_house) != 2:
                        valid = False
                        continue
                    
                    # Clue 13: Alice is the photography enthusiast.
                    for house in houses:
                        if assignment[house]['name'] == 'Alice' and assignment[house]['hobby'] != 'photography':
                            valid = False
                            break
                        if assignment[house]['hobby'] == 'photography' and assignment[house]['name'] != 'Alice':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 14: The person who enjoys gardening is Eric.
                    for house in houses:
                        if assignment[house]['hobby'] == 'gardening' and assignment[house]['name'] != 'Eric':
                            valid = False
                            break
                        if assignment[house]['name'] == 'Eric' and assignment[house]['hobby'] != 'gardening':
                            valid = False
                            break
                    if not valid:
                        continue
                    
                    # Clue 15: Bob is in the third house.
                    if assignment[3]['name'] != 'Bob':
                        valid = False
                        continue
                    
                    # If we reach here, all constraints are satisfied
                    if valid:
                        # Format the solution
                        rows = []
                        for house in sorted(assignment.keys()):
                            row = [
                                str(house),
                                assignment[house]['name'],
                                assignment[house]['style'],
                                assignment[house]['music'],
                                assignment[house]['hobby']
                            ]
                            rows.append(row)
                        
                        result = {
                            "solution": {
                                "header": ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"],
                                "rows": rows
                            }
                        }
                        
                        print(json.dumps(result, indent=2))
                        return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}))

if __name__ == "__main__":
    main()