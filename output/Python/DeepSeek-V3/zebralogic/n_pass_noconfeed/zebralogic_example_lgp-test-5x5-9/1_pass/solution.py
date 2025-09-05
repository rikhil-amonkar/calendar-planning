import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for drink_perm in permutations(drinks):
            for color_perm in permutations(colors):
                for flower_perm in permutations(flowers):
                    for hobby_perm in permutations(hobbies):
                        # Create assignment dictionaries for each house
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                'name': name_perm[i],
                                'drink': drink_perm[i],
                                'color': color_perm[i],
                                'flower': flower_perm[i],
                                'hobby': hobby_perm[i]
                            }
                        
                        # Check all constraints
                        # Clue 1: Alice is not in the fourth house.
                        if assignment[4]['name'] == 'Alice':
                            continue
                        
                        # Clue 2: The root beer lover is the person who enjoys gardening.
                        for house in houses:
                            if assignment[house]['drink'] == 'root beer' and assignment[house]['hobby'] != 'gardening':
                                break
                        else:
                            continue
                        
                        # Clue 3: The person whose favorite color is green is the coffee drinker.
                        for house in houses:
                            if assignment[house]['color'] == 'green' and assignment[house]['drink'] != 'coffee':
                                break
                        else:
                            continue
                        
                        # Clue 4: The person whose favorite color is green is the person who loves the bouquet of lilies.
                        for house in houses:
                            if assignment[house]['color'] == 'green' and assignment[house]['flower'] != 'lilies':
                                break
                        else:
                            continue
                        
                        # Clue 5: The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
                        blue_house = None
                        daffodils_house = None
                        for house in houses:
                            if assignment[house]['color'] == 'blue':
                                blue_house = house
                            if assignment[house]['flower'] == 'daffodils':
                                daffodils_house = house
                        if blue_house is None or daffodils_house is None or blue_house <= daffodils_house:
                            continue
                        
                        # Clue 6: The person who loves cooking is the person who loves blue.
                        for house in houses:
                            if assignment[house]['hobby'] == 'cooking' and assignment[house]['color'] != 'blue':
                                break
                        else:
                            continue
                        
                        # Clue 7: Eric is directly left of the tea drinker.
                        eric_house = None
                        tea_house = None
                        for house in houses:
                            if assignment[house]['name'] == 'Eric':
                                eric_house = house
                            if assignment[house]['drink'] == 'tea':
                                tea_house = house
                        if eric_house is None or tea_house is None or tea_house - eric_house != 1:
                            continue
                        
                        # Clue 8: The one who only drinks water is Peter.
                        for house in houses:
                            if assignment[house]['drink'] == 'water' and assignment[house]['name'] != 'Peter':
                                break
                        else:
                            continue
                        
                        # Clue 9: Arnold is the photography enthusiast.
                        for house in houses:
                            if assignment[house]['name'] == 'Arnold' and assignment[house]['hobby'] != 'photography':
                                break
                        else:
                            continue
                        
                        # Clue 10: The person who loves white is the person who loves the rose bouquet.
                        for house in houses:
                            if assignment[house]['color'] == 'white' and assignment[house]['flower'] != 'roses':
                                break
                        else:
                            continue
                        
                        # Clue 11: There is one house between the person who loves a carnations arrangement and the person whose favorite color is red.
                        carnations_house = None
                        red_house = None
                        for house in houses:
                            if assignment[house]['flower'] == 'carnations':
                                carnations_house = house
                            if assignment[house]['color'] == 'red':
                                red_house = house
                        if carnations_house is None or red_house is None or abs(carnations_house - red_house) != 2:
                            continue
                        
                        # Clue 12: The person who loves cooking is somewhere to the left of the person who paints as a hobby.
                        cooking_house = None
                        painting_house = None
                        for house in houses:
                            if assignment[house]['hobby'] == 'cooking':
                                cooking_house = house
                            if assignment[house]['hobby'] == 'painting':
                                painting_house = house
                        if cooking_house is None or painting_house is None or cooking_house >= painting_house:
                            continue
                        
                        # Clue 13: The one who only drinks water is in the third house.
                        if assignment[3]['drink'] != 'water':
                            continue
                        
                        # Clue 14: The person who loves a carnations arrangement is the root beer lover.
                        for house in houses:
                            if assignment[house]['flower'] == 'carnations' and assignment[house]['drink'] != 'root beer':
                                break
                        else:
                            continue
                        
                        # Clue 15: The person who loves white is in the second house.
                        if assignment[2]['color'] != 'white':
                            continue
                        
                        # If we reach here, all constraints are satisfied
                        # Prepare the solution in the required format
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                                "rows": []
                            }
                        }
                        
                        for house in sorted(assignment.keys()):
                            row = [
                                str(house),
                                assignment[house]['name'],
                                assignment[house]['drink'],
                                assignment[house]['color'],
                                assignment[house]['flower'],
                                assignment[house]['hobby']
                            ]
                            solution["solution"]["rows"].append(row)
                        
                        print(json.dumps(solution, indent=2))
                        return
    
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()