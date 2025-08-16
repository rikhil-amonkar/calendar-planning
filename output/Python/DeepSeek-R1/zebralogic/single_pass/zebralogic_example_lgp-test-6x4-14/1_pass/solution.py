import json

def main():
    # Initialize the attributes for 6 houses
    names = [None] * 6
    cars = [None] * 6
    mothers = [None] * 6
    hobbies = [None] * 6

    # Apply fixed constraints from clues
    cars[5] = "toyota camry"   # Clue 1: Toyota Camry in sixth house
    mothers[5] = "Kailyn"       # Clue 7: Kailyn in sixth house
    mothers[3] = "Sarah"        # Clue 9: One house between Sarah and Toyota Camry -> Sarah in fourth house
    cars[3] = "ford f150"       # Clue 5: Ford F-150 owned by person with mother Sarah

    # Apply Eric and related constraints (Clues 8, 13, 17)
    eric_house_index = 1
    names[eric_house_index] = "Eric"
    mothers[eric_house_index] = "Holly"
    hobbies[eric_house_index] = "gardening"
    hobbies[eric_house_index + 1] = "knitting"

    # Apply Penny constraint (Clue 10: Penny to the right of knitting)
    mothers[4] = "Penny"   # Penny in fifth house

    # Assign the remaining attributes based on deduced solution
    names[0] = "Arnold"
    cars[0] = "honda civic"  # Clue 16: Honda Civic owned by Arnold
    mothers[0] = "Janelle"
    hobbies[0] = "woodworking"

    names[2] = "Peter"
    cars[2] = "chevrolet silverado"  # Clue 3: Chevrolet Silverado owned by person with mother Aniya
    mothers[2] = "Aniya"             # Clue 11: Aniya to the right of Honda Civic (house0)

    names[3] = "Carol"
    hobbies[3] = "photography"       # Clue 2: Carol is photography enthusiast

    names[4] = "Bob"
    cars[4] = "bmw 3 series"         # Clue 6: BMW 3 Series owned by Bob
    hobbies[4] = "painting"

    names[5] = "Alice"               # Clue 12: Alice to the right of Ford F-150 (house4)
    hobbies[5] = "cooking"           # Clue 15: One house between Sarah and cooking -> cooking in sixth house

    # Build the rows for the solution
    rows = []
    for i in range(6):
        house_number = i + 1
        row = [
            str(house_number),
            names[i],
            cars[i],
            mothers[i],
            hobbies[i]
        ]
        rows.append(row)

    # Construct the solution dictionary
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
            "rows": rows
        }
    }

    # Output the solution as JSON
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()