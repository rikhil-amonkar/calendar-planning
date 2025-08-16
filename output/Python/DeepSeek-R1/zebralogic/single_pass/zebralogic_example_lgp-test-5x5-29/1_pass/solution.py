import json

def main():
    # Define the solution based on deductive reasoning
    solution = {
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": [
                ["1", "Alice", "german", "beach", "doctorate", "doctor"],
                ["2", "Arnold", "norwegian", "cruise", "associate", "lawyer"],
                ["3", "Bob", "dane", "city", "bachelor", "engineer"],
                ["4", "Eric", "brit", "camping", "master", "teacher"],
                ["5", "Peter", "swede", "mountain", "high school", "artist"]
            ]
        }
    }
    
    # Verify the solution against all clues
    if verify_solution(solution):
        print(json.dumps(solution))
    else:
        # Fallback to empty if verification fails (though expected to pass)
        print(json.dumps({"solution": {"header": [], "rows": []}}))

def verify_solution(solution_dict):
    rows = solution_dict["solution"]["rows"]
    # Extract the data into a list of dictionaries for easier access
    houses = []
    for row in rows:
        house_num = row[0]
        data = {
            'name': row[1],
            'nationality': row[2],
            'vacation': row[3],
            'education': row[4],
            'occupation': row[5]
        }
        houses.append(data)
    
    # Clue 1: Cruise vacation is the lawyer
    for house in houses:
        if house['vacation'] == 'cruise':
            if house['occupation'] != 'lawyer':
                return False
        if house['occupation'] == 'lawyer':
            if house['vacation'] != 'cruise':
                return False
    
    # Clue 2: Beach vacation is directly left of Arnold
    found = False
    for i in range(4):  # Check first 4 houses
        if houses[i]['vacation'] == 'beach' and houses[i+1]['name'] == 'Arnold':
            found = True
            break
    if not found:
        return False
    
    # Clue 3: Doctorate education is left of Bob
    doctorate_index = None
    bob_index = None
    for i, house in enumerate(houses):
        if house['education'] == 'doctorate':
            doctorate_index = i
        if house['name'] == 'Bob':
            bob_index = i
    if doctorate_index is None or bob_index is None or doctorate_index >= bob_index:
        return False
    
    # Clue 4: Associate education is cruise vacation
    for house in houses:
        if house['education'] == 'associate':
            if house['vacation'] != 'cruise':
                return False
        if house['vacation'] == 'cruise':
            if house['education'] != 'associate':
                return False
    
    # Clue 5: Peter is not in the first house
    if houses[0]['name'] == 'Peter':
        return False
    
    # Clue 6: The artist is Peter
    found = False
    for house in houses:
        if house['occupation'] == 'artist':
            if house['name'] == 'Peter':
                found = True
            else:
                return False
    if not found:
        return False
    
    # Clue 7: Camping vacation is master education
    for house in houses:
        if house['vacation'] == 'camping':
            if house['education'] != 'master':
                return False
        if house['education'] == 'master':
            if house['vacation'] != 'camping':
                return False
    
    # Clue 8: The Dane is to the right of the doctor
    doctor_index = None
    dane_index = None
    for i, house in enumerate(houses):
        if house['occupation'] == 'doctor':
            doctor_index = i
        if house['nationality'] == 'dane':
            dane_index = i
    if doctor_index is None or dane_index is None or doctor_index >= dane_index:
        return False
    
    # Clue 9: Associate education is directly left of the engineer
    found = False
    for i in range(4):
        if houses[i]['education'] == 'associate' and houses[i+1]['occupation'] == 'engineer':
            found = True
            break
    if not found:
        return False
    
    # Clue 10: Camping vacation is British
    for house in houses:
        if house['vacation'] == 'camping':
            if house['nationality'] != 'brit':
                return False
        if house['nationality'] == 'brit':
            if house['vacation'] != 'camping':
                return False
    
    # Clue 11: Norwegian and bachelor are adjacent
    norwegian_index = None
    bachelor_index = None
    for i, house in enumerate(houses):
        if house['nationality'] == 'norwegian':
            norwegian_index = i
        if house['education'] == 'bachelor':
            bachelor_index = i
    if norwegian_index is None or bachelor_index is None or abs(norwegian_index - bachelor_index) != 1:
        return False
    
    # Clue 12: The artist is Swedish
    for house in houses:
        if house['occupation'] == 'artist':
            if house['nationality'] != 'swede':
                return False
        if house['nationality'] == 'swede':
            if house['occupation'] != 'artist':
                return False
    
    # Clue 13: Bob is not in the fourth house
    if houses[3]['name'] == 'Bob':  # Fourth house is index 3
        return False
    
    # Clue 14: Camping vacation is Eric
    for house in houses:
        if house['vacation'] == 'camping':
            if house['name'] != 'Eric':
                return False
        if house['name'] == 'Eric':
            if house['vacation'] != 'camping':
                return False
    
    # Clue 15: Alice is German
    for house in houses:
        if house['name'] == 'Alice':
            if house['nationality'] != 'german':
                return False
        if house['nationality'] == 'german':
            if house['name'] != 'Alice':
                return False
    
    # Clue 16: Beach vacation is left of city vacation
    beach_index = None
    city_index = None
    for i, house in enumerate(houses):
        if house['vacation'] == 'beach':
            beach_index = i
        if house['vacation'] == 'city':
            city_index = i
    if beach_index is None or city_index is None or beach_index >= city_index:
        return False
    
    # Clue 17: Mountain vacation is in the fifth house
    if houses[4]['vacation'] != 'mountain':
        return False
    
    # Clue 18: Cruise vacation is right of beach vacation
    if beach_index is None or city_index is None:  # Reuse from clue 16
        return False
    cruise_index = None
    for i, house in enumerate(houses):
        if house['vacation'] == 'cruise':
            cruise_index = i
            break
    if beach_index >= cruise_index:
        return False
    
    # Clue 19: Bachelor education is in the third house
    if houses[2]['education'] != 'bachelor':
        return False
    
    return True

if __name__ == "__main__":
    main()