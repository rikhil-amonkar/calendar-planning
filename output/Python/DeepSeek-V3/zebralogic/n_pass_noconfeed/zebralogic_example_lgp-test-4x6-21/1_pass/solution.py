import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Peter', 'Arnold', 'Alice', 'Eric']
    flowers = ['roses', 'daffodils', 'carnations', 'lilies']
    hobbies = ['photography', 'painting', 'cooking', 'gardening']
    pets = ['dog', 'fish', 'bird', 'cat']
    colors = ['red', 'yellow', 'green', 'white']
    house_styles = ['craftsman', 'colonial', 'ranch', 'victorian']
    houses = ['1', '2', '3', '4']
    
    # Generate all possible permutations for each category
    name_perms = list(permutations(names))
    flower_perms = list(permutations(flowers))
    hobby_perms = list(permutations(hobbies))
    pet_perms = list(permutations(pets))
    color_perms = list(permutations(colors))
    house_style_perms = list(permutations(house_styles))
    
    # Try all combinations until we find one that satisfies all constraints
    for name_assignment in name_perms:
        for flower_assignment in flower_perms:
            for hobby_assignment in hobby_perms:
                for pet_assignment in pet_perms:
                    for color_assignment in color_perms:
                        for house_style_assignment in house_style_perms:
                            # Create assignment dictionaries for each house
                            assignment = {}
                            for i in range(4):
                                house_num = str(i + 1)
                                assignment[house_num] = {
                                    'Name': name_assignment[i],
                                    'Flower': flower_assignment[i],
                                    'Hobby': hobby_assignment[i],
                                    'Pet': pet_assignment[i],
                                    'Color': color_assignment[i],
                                    'HouseStyle': house_style_assignment[i]
                                }
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: The person in a Craftsman-style house is Arnold.
                            craftsman_house = None
                            for house, attrs in assignment.items():
                                if attrs['HouseStyle'] == 'craftsman':
                                    craftsman_house = house
                                    break
                            if craftsman_house and assignment[craftsman_house]['Name'] != 'Arnold':
                                valid = False
                            
                            # Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
                            rose_house = None
                            peter_house = None
                            for house, attrs in assignment.items():
                                if attrs['Flower'] == 'roses':
                                    rose_house = house
                                if attrs['Name'] == 'Peter':
                                    peter_house = house
                            if rose_house and peter_house and int(rose_house) <= int(peter_house):
                                valid = False
                            
                            # Clue 3: The photography enthusiast is the person who owns a dog.
                            for house, attrs in assignment.items():
                                if attrs['Hobby'] == 'photography' and attrs['Pet'] != 'dog':
                                    valid = False
                                if attrs['Pet'] == 'dog' and attrs['Hobby'] != 'photography':
                                    valid = False
                            
                            # Clue 4: The person who loves a bouquet of daffodils is not in the fourth house.
                            if assignment['4']['Flower'] == 'daffodils':
                                valid = False
                            
                            # Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
                            for house, attrs in assignment.items():
                                if attrs['Flower'] == 'roses' and attrs['Color'] != 'red':
                                    valid = False
                                if attrs['Color'] == 'red' and attrs['Flower'] != 'roses':
                                    valid = False
                            
                            # Clue 6: The person in a Craftsman-style house is in the second house.
                            if assignment['2']['HouseStyle'] != 'craftsman':
                                valid = False
                            
                            # Clue 7: Eric is the person residing in a Victorian house.
                            for house, attrs in assignment.items():
                                if attrs['Name'] == 'Eric' and attrs['HouseStyle'] != 'victorian':
                                    valid = False
                                if attrs['HouseStyle'] == 'victorian' and attrs['Name'] != 'Eric':
                                    valid = False
                            
                            # Clue 8: The person with an aquarium of fish is the person who loves white.
                            for house, attrs in assignment.items():
                                if attrs['Pet'] == 'fish' and attrs['Color'] != 'white':
                                    valid = False
                                if attrs['Color'] == 'white' and attrs['Pet'] != 'fish':
                                    valid = False
                            
                            # Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
                            cooking_house = None
                            red_house = None
                            for house, attrs in assignment.items():
                                if attrs['Hobby'] == 'cooking':
                                    cooking_house = house
                                if attrs['Color'] == 'red':
                                    red_house = house
                            if cooking_house and red_house and int(cooking_house) <= int(red_house):
                                valid = False
                            
                            # Clue 10: The person who loves white is the person who loves a carnations arrangement.
                            for house, attrs in assignment.items():
                                if attrs['Color'] == 'white' and attrs['Flower'] != 'carnations':
                                    valid = False
                                if attrs['Flower'] == 'carnations' and attrs['Color'] != 'white':
                                    valid = False
                            
                            # Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
                            white_house = None
                            gardening_house = None
                            for house, attrs in assignment.items():
                                if attrs['Color'] == 'white':
                                    white_house = house
                                if attrs['Hobby'] == 'gardening':
                                    gardening_house = house
                            if white_house and gardening_house and int(white_house) <= int(gardening_house):
                                valid = False
                            
                            # Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
                            for house, attrs in assignment.items():
                                if attrs['Flower'] == 'daffodils' and attrs['Color'] != 'yellow':
                                    valid = False
                                if attrs['Color'] == 'yellow' and attrs['Flower'] != 'daffodils':
                                    valid = False
                            
                            # Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
                            for house, attrs in assignment.items():
                                if attrs['HouseStyle'] == 'colonial' and attrs['Color'] != 'red':
                                    valid = False
                                if attrs['Color'] == 'red' and attrs['HouseStyle'] != 'colonial':
                                    valid = False
                            
                            # Clue 14: The person who has a cat is Eric.
                            for house, attrs in assignment.items():
                                if attrs['Pet'] == 'cat' and attrs['Name'] != 'Eric':
                                    valid = False
                                if attrs['Name'] == 'Eric' and attrs['Pet'] != 'cat':
                                    valid = False
                            
                            if valid:
                                # Found valid solution, format output
                                rows = []
                                for house in houses:
                                    attrs = assignment[house]
                                    rows.append([
                                        house,
                                        attrs['Name'],
                                        attrs['Flower'],
                                        attrs['Hobby'],
                                        attrs['Pet'],
                                        attrs['Color'],
                                        attrs['HouseStyle']
                                    ])
                                
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                                        "rows": rows
                                    }
                                }
                                
                                print(json.dumps(result, indent=2))
                                return
    
    print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()