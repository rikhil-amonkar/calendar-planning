import json

def main():
    # Fixed assignments
    house4 = ('4', 'Alice', 'Alice', 'watermelon')
    house6 = ('6', None, 'Meredith', 'dragonfruit')  # name to be determined
    house3_child = 'Samantha'
    house2_smoothie = 'cherry'
    
    # Deduced fixed values
    house1_smoothie = 'blueberry'
    house2_child = 'Fred'
    house3_smoothie = 'dessert'  # Corrected typo: 'desert' -> 'dessert'
    house5_smoothie = 'lime'
    
    # Possible values for the remaining attributes
    names = ['Arnold', 'Peter', 'Carol', 'Bob', 'Eric']
    children = ['Timothy', 'Bella']  # Only Timothy and Bella left for houses 1 and 5
    
    # Iterate over possibilities
    for name1 in names:
        for child1 in children:
            # Determine child5: the other child
            child5 = 'Bella' if child1 == 'Timothy' else 'Timothy'
            for name2 in [n for n in names if n != name1]:
                for name3 in [n for n in names if n not in [name1, name2]]:
                    remaining_names = [n for n in names if n not in [name1, name2, name3]]
                    if len(remaining_names) != 2:
                        continue
                    name5, name6 = remaining_names
                    # Check clue8: Peter in house5 or house6
                    if 'Peter' not in [name5, name6]:
                        continue
                    # Check clue10: Bob is mother of Timothy
                    if (name1 == 'Bob' and child1 != 'Timothy') or (name1 != 'Bob' and child1 == 'Timothy'):
                        continue
                    if (name5 == 'Bob' and child5 != 'Timothy') or (name5 != 'Bob' and child5 == 'Timothy'):
                        continue
                    # Bob cannot be in other houses due to child constraints
                    if name2 == 'Bob' or name3 == 'Bob' or name6 == 'Bob':
                        continue
                    # Create assignment
                    assignment = [
                        ['1', name1, child1, house1_smoothie],
                        ['2', name2, house2_child, house2_smoothie],
                        ['3', name3, house3_child, house3_smoothie],
                        list(house4),
                        ['5', name5, child5, house5_smoothie],
                        ['6', name6, house6[2], house6[3]]
                    ]
                    # Check clue11: Arnold directly left of Carol
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