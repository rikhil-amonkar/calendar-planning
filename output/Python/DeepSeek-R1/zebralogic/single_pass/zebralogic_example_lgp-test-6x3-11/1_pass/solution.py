import json

def main():
    # Initialize the houses: list of 6 dictionaries, each for house index 0 to 5 (representing house1 to house6)
    houses = [{'Name': None, 'HairColor': None, 'Height': None} for _ in range(6)]
    
    # Apply direct clues
    # Clue 2: Alice is in the fourth house (index 3)
    houses[3]['Name'] = 'Alice'
    # Clue 4: The person who is tall is in the sixth house (index 5)
    houses[5]['Height'] = 'tall'
    # Clue 10: The person who is very short is in the fifth house (index 4)
    houses[4]['Height'] = 'very short'
    # Clue 12: The person who has gray hair is in the third house (index 2)
    houses[2]['HairColor'] = 'gray'
    
    # Clue 8: The person who has blonde hair is Carol
    # Clue 13: The person who has blonde hair is very tall -> Carol has blonde hair and is very tall
    # Clue 11: Bob has brown hair
    
    # Apply clue 1: The person with blonde hair (Carol) is directly left of Bob
    # Carol must be in house1 (index0) and Bob in house2 (index1)
    houses[0]['Name'] = 'Carol'
    houses[0]['HairColor'] = 'blonde'
    houses[0]['Height'] = 'very tall'
    houses[1]['Name'] = 'Bob'
    houses[1]['HairColor'] = 'brown'
    
    # Clue 9: One house between gray hair (house3, index2) and red hair -> red hair must be in house5 (index4)
    houses[4]['HairColor'] = 'red'
    # Clue 6: The person with red hair is Eric -> house5: Eric
    houses[4]['Name'] = 'Eric'
    
    # Clue 3: The person who is short is Arnold -> Arnold must be assigned to a house with height 'short'
    # Remaining houses: index2 (house3) and index5 (house6). House6 has height 'tall', so Arnold must be in house3 (index2)
    houses[2]['Name'] = 'Arnold'
    houses[2]['Height'] = 'short'
    
    # Only name left for house6 (index5) is Peter
    houses[5]['Name'] = 'Peter'
    
    # Hair colors left: auburn and black for houses index3 (house4) and index5 (house6)
    # Clue 5: Black hair not in fourth house (index3) -> house4 gets auburn, house6 gets black
    houses[3]['HairColor'] = 'auburn'
    houses[5]['HairColor'] = 'black'
    
    # Heights left: average and super tall for house2 (index1) and house4 (index3)
    # Clue 7: Super tall is to the right of average -> house2: average, house4: super tall
    houses[1]['Height'] = 'average'
    houses[3]['Height'] = 'super tall'
    
    # Prepare the solution in the required JSON format
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": []
        }
    }
    
    # Populate rows: house number, name, hair color, height
    for i in range(6):
        house_num = str(i+1)
        name = houses[i]['Name']
        hair_color = houses[i]['HairColor']
        height = houses[i]['Height']
        solution["solution"]["rows"].append([house_num, name, hair_color, height])
    
    # Output as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()