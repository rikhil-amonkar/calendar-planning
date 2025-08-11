import json

def main():
    # Initialize the two houses
    house1 = {'House': '1', 'name': None, 'house_style': None, 'height': None, 'education': None}
    house2 = {'House': '2', 'name': None, 'house_style': None, 'height': None, 'education': None}
    houses = [house1, house2]
    
    # Apply clue 2: Victorian house is in the first house
    houses[0]['house_style'] = 'victorian'
    
    # Apply clue 1: The short person is directly left of Eric
    houses[0]['height'] = 'short'
    houses[1]['name'] = 'Eric'
    
    # Apply clue 3: The short person has an associate's degree
    houses[0]['education'] = 'associate'
    
    # Assign the remaining attributes
    houses[0]['name'] = 'Arnold'
    houses[1]['house_style'] = 'colonial'
    houses[1]['height'] = 'very short'
    houses[1]['education'] = 'high school'
    
    # Prepare the solution dictionary
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "House Style", "Height", "Education"],
            "rows": [
                [houses[0]['House'], houses[0]['name'], houses[0]['house_style'], houses[0]['height'], houses[0]['education']],
                [houses[1]['House'], houses[1]['name'], houses[1]['house_style'], houses[1]['height'], houses[1]['education']]
            ]
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()