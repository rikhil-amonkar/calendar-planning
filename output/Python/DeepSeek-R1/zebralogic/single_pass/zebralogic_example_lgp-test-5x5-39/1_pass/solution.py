import json

def main():
    # Define the attributes and their possible values
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold']
    birthdays = ['mar', 'april', 'sept', 'feb', 'jan']
    mothers = ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya']
    occupations = ['engineer', 'doctor', 'lawyer', 'artist', 'teacher']
    hair_colors = ['red', 'blonde', 'black', 'gray', 'brown']
    
    # Initialize the solution grid: 5 houses, each with 5 attributes
    houses = [
        {'Name': None, 'Birthday': None, 'Mother': None, 'Occupation': None, 'HairColor': None},
        {'Name': None, 'Birthday': None, 'Mother': None, 'Occupation': None, 'HairColor': None},
        {'Name': None, 'Birthday': None, 'Mother': None, 'Occupation': None, 'HairColor': None},
        {'Name': None, 'Birthday': None, 'Mother': None, 'Occupation': None, 'HairColor': None},
        {'Name': None, 'Birthday': None, 'Mother': None, 'Occupation': None, 'HairColor': None}
    ]
    
    # Apply direct assignments from clues
    # Clue 1: March birthday in house 5
    houses[4]['Birthday'] = 'mar'
    # Clue 2: February birthday in house 1
    houses[0]['Birthday'] = 'feb'
    # Clue 4: Janelle as mother in house 3
    houses[2]['Mother'] = 'Janelle'
    # Clue 6: Artist in house 4
    houses[3]['Occupation'] = 'artist'
    # Clue 5: Artist has brown hair -> house 4 has brown hair
    houses[3]['HairColor'] = 'brown'
    # Clue 12: Brown hair means January birthday -> house 4 has January birthday
    houses[3]['Birthday'] = 'jan'
    # Clue 3: Eric is the doctor
    # Clue 8: Peter has black hair
    # Clue 15: Peter is a lawyer
    # Clue 13: Arnold has blonde hair
    # Clue 17: Alice has gray hair
    # Clue 9: Gray hair means teacher -> Alice is teacher
    # Clue 10: Alice's mother is Kailyn
    # Clue 14: Holly as mother means black hair -> Peter has mother Holly (since Peter has black hair)
    
    # From the clues, we deduce:
    # House 5: March birthday, and Alice must be in a house with gray hair (teacher) and mother Kailyn.
    # Given house 4 is taken (brown hair), Alice cannot be there. Also, house 5 has March, so Alice is in house 5.
    houses[4]['Name'] = 'Alice'
    houses[4]['HairColor'] = 'gray'
    houses[4]['Occupation'] = 'teacher'
    houses[4]['Mother'] = 'Kailyn'
    
    # House 4: We know artist and brown hair and January birthday. The name cannot be Alice, Eric (doctor), Peter (lawyer, black hair), Arnold (blonde) -> must be Bob.
    houses[3]['Name'] = 'Bob'
    
    # Birthdays left: april and sept for houses 1 and 2 (house 0 has feb, house 3 has jan, house 4 has mar)
    # House 0 has feb, house 3 has jan, house 4 has mar -> houses 1 and 2 have april and sept.
    # Clue 16: September birthday is left of Alice's mother (house 5). So September must be in house 1 or 2.
    # Clue 11: Arnold is right of September birthday. Arnold cannot be in house 4 (Bob) or 5 (Alice) -> so in house 1,2,3.
    # If house 2 has sept, then Arnold can be in house 2,3,4,5 -> but 4 and 5 taken, so house 3. But house 3 has birthday? not set -> could be april.
    # If house 1 has sept, then Arnold in house 2,3,4,5 -> 4 and 5 taken, so house 2 or 3.
    # Also, from clue 8 and 15: Peter has black hair and is lawyer -> we don't know house yet.
    # Clue 7: Penny (mother) is left of black hair (Peter's house).
    
    # After deduction (as in hand solution):
    # House 0: Eric, doctor, red hair, Penny, feb birthday
    houses[0]['Name'] = 'Eric'
    houses[0]['Occupation'] = 'doctor'
    houses[0]['HairColor'] = 'red'
    houses[0]['Mother'] = 'Penny'
    
    # House 1: Peter, lawyer, black hair, Holly, sept birthday
    houses[1]['Name'] = 'Peter'
    houses[1]['Occupation'] = 'lawyer'
    houses[1]['HairColor'] = 'black'
    houses[1]['Mother'] = 'Holly'
    houses[1]['Birthday'] = 'sept'
    
    # House 2: Arnold, engineer, blonde hair, Janelle, april birthday
    houses[2]['Name'] = 'Arnold'
    houses[2]['Occupation'] = 'engineer'
    houses[2]['HairColor'] = 'blonde'
    houses[2]['Birthday'] = 'april'
    
    # House 3: Bob, artist, brown hair, Aniya, jan birthday (already set)
    houses[3]['Mother'] = 'Aniya'
    
    # House 4: Alice, teacher, gray hair, Kailyn, mar birthday (already set)
    
    # Prepare the output in the required JSON format
    header = ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"]
    rows = []
    for i in range(5):
        house_num = str(i+1)
        name = houses[i]['Name']
        birthday = houses[i]['Birthday']
        mother = houses[i]['Mother']
        occupation = houses[i]['Occupation']
        hair_color = houses[i]['HairColor']
        rows.append([house_num, name, birthday, mother, occupation, hair_color])
    
    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()