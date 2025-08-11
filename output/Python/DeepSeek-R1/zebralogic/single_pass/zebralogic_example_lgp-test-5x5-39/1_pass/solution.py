import json

def main():
    # Initialize the attributes for the houses (index 0 to 4 for house1 to house5)
    names = [None] * 5
    months = [None] * 5
    mothers = [None] * 5
    occupations = [None] * 5
    hairs = [None] * 5

    # Set the fixed values from the clues
    months[0] = 'feb'   # Clue2: February in first house
    months[4] = 'mar'   # Clue1: March in fifth house
    months[3] = 'jan'   # Clue6: artist in fourth house and Clue12: brown hair has January birthday
    occupations[3] = 'artist'  # Clue6: artist in fourth house
    hairs[3] = 'brown'  # Clue5: artist has brown hair
    mothers[2] = 'Janelle'  # Clue4: Janelle in third house
    names[3] = 'Bob'    # Deduced: only Bob can be in house4

    # Apply constraints to deduce the remaining values
    names[0] = 'Eric'
    occupations[0] = 'doctor'   # Clue3: Eric is the doctor
    hairs[0] = 'red'            # Only hair color left for Eric
    mothers[0] = 'Penny'        # Deduced from constraints

    names[1] = 'Peter'
    occupations[1] = 'lawyer'   # Clue15: Peter is lawyer
    hairs[1] = 'black'          # Clue8: Peter has black hair
    mothers[1] = 'Holly'        # Clue14: mother Holly has black hair

    names[2] = 'Arnold'
    occupations[2] = 'engineer' # Only occupation left
    hairs[2] = 'blonde'         # Clue13: Arnold has blonde hair
    # mothers[2] is already 'Janelle'

    names[4] = 'Alice'
    mothers[4] = 'Kailyn'       # Clue10: Alice has mother Kailyn
    occupations[4] = 'teacher'  # Clue9: gray hair is teacher and Clue17: Alice has gray hair
    hairs[4] = 'gray'           # Clue17: Alice has gray hair

    months[1] = 'sept'          # Deduced from constraints
    months[2] = 'april'         # Only month left

    # Prepare the solution in the required JSON format
    header = ["House", "Name", "birthday month", "mother's name", "occupation", "hair color"]
    rows = []
    for i in range(5):
        house_number = str(i+1)
        row = [house_number, names[i], months[i], mothers[i], occupations[i], hairs[i]]
        rows.append(row)
    
    solution_json = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution_json))

if __name__ == "__main__":
    main()