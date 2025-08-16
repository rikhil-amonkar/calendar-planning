import json

def main():
    # Initialize attributes
    names = [None] * 5
    hobbies = [None] * 5
    heights = [None] * 5
    foods = [None] * 5

    # Set fixed attributes from clues
    heights[2] = 'tall'          # house3 (clue 13)
    heights[4] = 'very short'     # house5 (clue 12)
    foods[2] = 'grilled cheese'   # house3 (clue 2 and 13)
    foods[3] = 'stir fry'         # house4 (clue 4)
    hobbies[1] = 'painting'       # house2 (clue 11)

    # Deduce food assignments
    foods[4] = 'pizza'            # house5 (clue 6: Alice left of pizza)
    names[3] = 'Alice'            # house4 (clue 6 and 14)
    foods[0] = 'spaghetti'        # house1 (clue 7)
    foods[1] = 'stew'             # house2 (remaining food)

    # Assign names
    names[0] = 'Peter'            # house1 (clue 3 and 9)
    heights[0] = 'short'          # house1 (clue 9)
    names[2] = 'Bob'              # house3 (clue 1 and 14)
    hobbies[2] = 'photography'    # house3 (clue 1)
    names[1] = 'Eric'             # house2 (clue 8)
    names[4] = 'Arnold'           # house5 (remaining name)

    # Assign remaining heights and hobbies
    heights[3] = 'average'        # house4 (clue 5)
    heights[1] = 'very tall'      # house2 (remaining height)
    hobbies[3] = 'cooking'        # house4 (clue 5)
    hobbies[4] = 'gardening'      # house5 (clue 10)
    hobbies[0] = 'knitting'       # house1 (remaining hobby)

    # Prepare solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": []
        }
    }
    
    # Populate rows for each house
    for i in range(5):
        house_number = str(i + 1)
        row = [house_number, names[i], hobbies[i], heights[i], foods[i]]
        solution["solution"]["rows"].append(row)
    
    # Output JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()