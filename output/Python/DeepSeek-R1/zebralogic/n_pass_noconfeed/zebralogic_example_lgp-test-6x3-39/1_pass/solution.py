import json

def main():
    # Pre-fixed assignments
    house4 = ('4', 'Alice', 'Alice', 'watermelon')
    house6 = ('6', None, 'Meredith', 'dragonfruit')  # name to be determined
    house3_child = 'Samantha'
    house2_smoothie = 'cherry'
    
    # Possible values for the remaining attributes
    names = ['Arnold', 'Peter', 'Carol', 'Bob', 'Eric']
    children = ['Timothy', 'Bella', 'Fred']
    smoothies = ['desert', 'blueberry', 'lime']
    
    # Iterate over all possibilities
    for name1 in names:
        for child1 in children:
            for smoothie1 in smoothies:
                for name2 in [n for n in names if n != name1]:
                    # Check clue9: Arnold not in house2
                    if name2 == 'Arnold':
                        continue
                    for child2 in [c for c in children if c != child1]:
                        for name3 in [n for n in names if n not in [name1, name2]]:
                            for smoothie3 in [s for s in smoothies if s != smoothie1]:
                                remaining_names = [n for n in names if n not in [name1, name2, name3]]
                                if len(remaining_names) != 2:
                                    continue
                                name5 = remaining_names[0]
                                name6 = remaining_names[1]
                                # Check clue8: Peter in house5 or house6
                                if 'Peter' not in [name5, name6]:
                                    continue
                                
                                remaining_children = [c for c in children if c not in [child1, child2]]
                                if len(remaining_children) != 1:
                                    continue
                                child5 = remaining_children[0]
                                
                                remaining_smoothies = [s for s in smoothies if s not in [smoothie1, smoothie3]]
                                if len(remaining_smoothies) != 1:
                                    continue
                                smoothie5 = remaining_smoothies[0]
                                
                                # Create temporary assignment
                                assignment = [
                                    ['1', name1, child1, smoothie1],
                                    ['2', name2, child2, house2_smoothie],
                                    ['3', name3, house3_child, smoothie3],
                                    list(house4),
                                    ['5', name5, child5, smoothie5],
                                    ['6', name6, house6[2], house6[3]]
                                ]
                                
                                # Check constraints
                                # clue1: child Fred and desert smoothie adjacent
                                fred_house = None
                                desert_house = None
                                for house in assignment:
                                    if house[2] == 'Fred':
                                        fred_house = int(house[0])
                                    if house[3] == 'desert':
                                        desert_house = int(house[0])
                                if fred_house is None or desert_house is None or abs(fred_house - desert_house) != 1:
                                    continue
                                
                                # clue2: blueberry left of child Fred
                                blueberry_house = None
                                for house in assignment:
                                    if house[3] == 'blueberry':
                                        blueberry_house = int(house[0])
                                if blueberry_house is None or blueberry_house >= fred_house:
                                    continue
                                
                                # clue8: Peter right of house3 (already ensured by Peter in 5 or 6)
                                # But double-check: house3 is number 3, so Peter must be in 4,5,6 but house4 is Alice, so 5 or 6.
                                peter_house = None
                                for house in assignment:
                                    if house[1] == 'Peter':
                                        peter_house = int(house[0])
                                if peter_house <= 3:
                                    continue
                                
                                # clue10: Bob is mother of Timothy
                                timothy_house = None
                                bob_house = None
                                for house in assignment:
                                    if house[2] == 'Timothy':
                                        timothy_house = int(house[0])
                                    if house[1] == 'Bob':
                                        bob_house = int(house[0])
                                if timothy_house != bob_house:
                                    continue
                                
                                # clue11: Arnold directly left of Carol
                                arnold_house = None
                                carol_house = None
                                for house in assignment:
                                    if house[1] == 'Arnold':
                                        arnold_house = int(house[0])
                                    if house[1] == 'Carol':
                                        carol_house = int(house[0])
                                if arnold_house is None or carol_house is None or arnold_house + 1 != carol_house:
                                    continue
                                
                                # Found solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Children", "Smoothie"],
                                        "rows": assignment
                                    }
                                }
                                print(json.dumps(solution, indent=2))
                                return
                                
    print("No solution found")

if __name__ == "__main__":
    main()