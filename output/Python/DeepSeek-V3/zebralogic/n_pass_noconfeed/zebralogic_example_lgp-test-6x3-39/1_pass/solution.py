import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Peter', 'Carol', 'Alice', 'Bob', 'Eric']
    children = ['Alice', 'Timothy', 'Bella', 'Meredith', 'Fred', 'Samantha']
    smoothies = ['desert', 'cherry', 'watermelon', 'blueberry', 'lime', 'dragonfruit']

    # Generate all possible permutations for names, children, and smoothies
    for name_perm in permutations(names):
        for child_perm in permutations(children):
            for smoothie_perm in permutations(smoothies):
                assignment = {}
                valid = True
                
                # Create assignment dictionary
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'name': name_perm[i],
                        'child': child_perm[i],
                        'smoothie': smoothie_perm[i]
                    }
                
                # Check clue 3: Alice is not in the fifth house
                if assignment[5]['name'] == 'Alice':
                    continue
                
                # Check clue 4: The person's child is named Samantha is not in the second house
                if assignment[2]['child'] == 'Samantha':
                    continue
                
                # Check clue 6: Alice is the person's child is named Alice
                # Find Alice (name) and check if her child is Alice
                for house in houses:
                    if assignment[house]['name'] == 'Alice':
                        if assignment[house]['child'] != 'Alice':
                            valid = False
                        break
                if not valid:
                    continue
                
                # Check clue 7: Alice is the Watermelon smoothie lover
                for house in houses:
                    if assignment[house]['name'] == 'Alice':
                        if assignment[house]['smoothie'] != 'watermelon':
                            valid = False
                        break
                if not valid:
                    continue
                
                # Check clue 9: Arnold is not in the second house
                if assignment[2]['name'] == 'Arnold':
                    continue
                
                # Check clue 10: Bob is the person who is the mother of Timothy
                for house in houses:
                    if assignment[house]['name'] == 'Bob':
                        if assignment[house]['child'] != 'Timothy':
                            valid = False
                        break
                if not valid:
                    continue
                
                # Check clue 11: Arnold is directly left of Carol
                arnold_house = None
                carol_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Arnold':
                        arnold_house = house
                    if assignment[house]['name'] == 'Carol':
                        carol_house = house
                if arnold_house is None or carol_house is None or arnold_house + 1 != carol_house:
                    continue
                
                # Check clue 13: The person's child is named Meredith is in the sixth house
                if assignment[6]['child'] != 'Meredith':
                    continue
                
                # Check clue 14: The Dragonfruit smoothie lover is the person's child is named Meredith
                if assignment[6]['smoothie'] != 'dragonfruit':
                    continue
                
                # Check clue 5: Watermelon smoothie lover is right of Cherry smoothie lover
                watermelon_house = None
                cherry_house = None
                for house in houses:
                    if assignment[house]['smoothie'] == 'watermelon':
                        watermelon_house = house
                    if assignment[house]['smoothie'] == 'cherry':
                        cherry_house = house
                if cherry_house is None or watermelon_house is None or cherry_house >= watermelon_house:
                    continue
                
                # Check clue 12: Cherry smoothie lover is directly left of child Samantha
                samantha_house = None
                for house in houses:
                    if assignment[house]['child'] == 'Samantha':
                        samantha_house = house
                        break
                if cherry_house is None or samantha_house is None or cherry_house + 1 != samantha_house:
                    continue
                
                # Check clue 2: Blueberry smoothie lover is left of Fred's child
                blueberry_house = None
                fred_house = None
                for house in houses:
                    if assignment[house]['smoothie'] == 'blueberry':
                        blueberry_house = house
                    if assignment[house]['child'] == 'Fred':
                        fred_house = house
                if blueberry_house is None or fred_house is None or blueberry_house >= fred_house:
                    continue
                
                # Check clue 1: Fred's child and Desert smoothie lover are adjacent
                desert_house = None
                for house in houses:
                    if assignment[house]['smoothie'] == 'desert':
                        desert_house = house
                        break
                if desert_house is None or abs(fred_house - desert_house) != 1:
                    continue
                
                # Check clue 8: Peter is right of child Samantha
                peter_house = None
                for house in houses:
                    if assignment[house]['name'] == 'Peter':
                        peter_house = house
                        break
                if peter_house is None or peter_house <= samantha_house:
                    continue
                
                # If we reach here, all constraints are satisfied
                result = {
                    "solution": {
                        "header": ["House", "Name", "Children", "Smoothie"],
                        "rows": []
                    }
                }
                
                for house in sorted(assignment.keys()):
                    row = [
                        str(house),
                        assignment[house]['name'],
                        assignment[house]['child'],
                        assignment[house]['smoothie']
                    ]
                    result["solution"]["rows"].append(row)
                
                print(json.dumps(result, indent=2))
                return
    
    print('{"solution": {"header": ["House", "Name", "Children", "Smoothie"], "rows": []}}')

if __name__ == "__main__":
    main()