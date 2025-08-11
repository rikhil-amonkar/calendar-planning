import json

def main():
    names = ['Eric', 'Arnold']
    sports = ['basketball', 'soccer']
    hobbies = ['photography', 'gardening']
    
    house1 = {'House': '1', 'Name': None, 'Favorite Sports': None, 'Hobby': None}
    house2 = {'House': '2', 'Name': None, 'Favorite Sports': None, 'Hobby': None}
    
    house1['Hobby'] = 'gardening'
    house1['Name'] = 'Arnold'
    house1['Favorite Sports'] = 'basketball'
    
    house2['Name'] = [name for name in names if name != house1['Name']][0]
    house2['Favorite Sports'] = [sport for sport in sports if sport != house1['Favorite Sports']][0]
    house2['Hobby'] = [hobby for hobby in hobbies if hobby != house1['Hobby']][0]
    
    header = ["House", "Name", "Favorite Sports", "Hobby"]
    rows = [
        [house1[attr] for attr in header],
        [house2[attr] for attr in header]
    ]
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()