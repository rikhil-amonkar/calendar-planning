import json

def main():
    houses = [{'House': str(i+1)} for i in range(4)]
    
    # House indices: 0: House1, 1: House2, 2: House3, 3: House4
    houses[2]['Education'] = 'high school'
    houses[2]['Birthday'] = 'sept'
    houses[2]['Smoothie'] = 'cherry'
    
    houses[0]['Smoothie'] = 'dragonfruit'
    
    houses[0]['Education'] = 'associate'
    houses[0]['Name'] = 'Arnold'
    houses[0]['Birthday'] = 'april'
    
    houses[1]['Education'] = 'bachelor'
    houses[1]['Name'] = 'Eric'
    houses[1]['Birthday'] = 'jan'
    houses[1]['Smoothie'] = 'desert'
    houses[1]['Hobby'] = 'gardening'
    
    houses[3]['Education'] = 'master'
    houses[3]['Name'] = 'Peter'
    houses[3]['Birthday'] = 'feb'
    houses[3]['Smoothie'] = 'watermelon'
    houses[3]['Hobby'] = 'painting'
    
    houses[2]['Name'] = 'Alice'
    houses[2]['Hobby'] = 'cooking'
    
    houses[0]['Hobby'] = 'photography'
    
    header = ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"]
    rows = []
    for house in houses:
        row = [
            house['House'],
            house.get('Name', ''),
            house.get('Hobby', ''),
            house.get('Birthday', ''),
            house.get('Education', ''),
            house.get('Smoothie', '')
        ]
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()