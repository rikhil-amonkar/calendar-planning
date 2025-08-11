import json

def main():
    # Initialize attributes for 6 houses (index 0 to 5 for house1 to house6)
    names = [None] * 6
    cars = [None] * 6
    mothers = [None] * 6
    hobbies = [None] * 6

    # Apply direct assignments from clues
    cars[5] = 'toyota camry'  # Clue1: house6 has toyota camry
    mothers[5] = 'Kailyn'      # Clue7: house6 has mother Kailyn
    mothers[3] = 'Sarah'       # Clue9: one house between Sarah and toyota -> house4 (index3)
    cars[3] = 'ford f150'      # Clue5: ford f150 has mother Sarah (house4)

    # Eric is at house2 (index1) with mother Holly and hobby gardening (from Clues8,13,17)
    names[1] = 'Eric'
    mothers[1] = 'Holly'
    hobbies[1] = 'gardening'

    # Knitting is directly right of Eric (house3, index2) from Clue8
    hobbies[2] = 'knitting'

    # Mother Penny is to the right of knitting -> house5 (index4) from Clue10
    mothers[4] = 'Penny'

    # Cooking hobby is at house6 (index5) from Clue15 (one house between Sarah and cooking)
    hobbies[5] = 'cooking'

    # Woodworking is left of knitting -> house1 (index0) from Clue14
    hobbies[0] = 'woodworking'

    # Mothers for house1 (index0) and house3 (index2): Janelle and Aniya (from constraints)
    mothers[0] = 'Janelle'
    mothers[2] = 'Aniya'

    # Chevrolet Silverado at house3 (index2) from Clue3 (mother Aniya)
    cars[2] = 'chevrolet silverado'

    # Honda Civic at house1 (index0) with name Arnold from Clue16
    cars[0] = 'honda civic'
    names[0] = 'Arnold'

    # Remaining cars: tesla model3 and bmw 3 series for house2 and house5
    # House2 (Eric) cannot have bmw (Clue6: Bob has bmw) -> house2 gets tesla, house5 gets bmw
    cars[1] = 'tesla model 3'
    cars[4] = 'bmw 3 series'
    names[4] = 'Bob'  # Clue6: bmw owner is Bob

    # Carol has photography hobby (Clue2) -> must be at house4 (index3)
    names[3] = 'Carol'
    hobbies[3] = 'photography'

    # House5 (index4) gets painting hobby (only remaining)
    hobbies[4] = 'painting'

    # Remaining names: Peter for house3 (index2), Alice for house6 (index5)
    names[2] = 'Peter'
    names[5] = 'Alice'

    # Prepare the solution dictionary
    solution = {
        "header": ["House", "Name", "Car", "Mother", "Hobby"],
        "rows": []
    }

    for i in range(6):
        house_number = str(i + 1)
        row = [
            house_number,
            names[i],
            cars[i],
            mothers[i],
            hobbies[i]
        ]
        solution["rows"].append(row)

    # Output as JSON
    result = {
        "solution": solution
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()