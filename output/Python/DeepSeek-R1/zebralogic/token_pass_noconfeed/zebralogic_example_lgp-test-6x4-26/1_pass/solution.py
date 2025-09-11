import json

def main():
    # Initialize the houses as a list of dictionaries
    houses = [{'name': None, 'pet': None, 'house_style': None, 'birthday': None} for _ in range(6)]
    
    # Assign known values from direct clues
    houses[1]['name'] = 'Peter'
    houses[1]['house_style'] = 'colonial'
    houses[1]['birthday'] = 'may'
    
    houses[2]['name'] = 'Carol'
    houses[2]['birthday'] = 'mar'
    
    houses[3]['name'] = 'Arnold'
    houses[3]['pet'] = 'dog'
    houses[3]['house_style'] = 'craftsman'
    
    houses[5]['name'] = 'Eric'
    
    # Deduce birthdays
    houses[3]['birthday'] = 'jan'
    houses[4]['birthday'] = 'april'
    houses[5]['birthday'] = 'sept'
    houses[0]['birthday'] = 'feb'
    
    # Deduce names
    houses[0]['name'] = 'Bob'
    houses[4]['name'] = 'Alice'
    
    # Deduce pets
    houses[5]['pet'] = 'hamster'
    houses[2]['pet'] = 'bird'
    houses[4]['pet'] = 'fish'
    houses[0]['pet'] = 'cat'
    houses[1]['pet'] = 'rabbit'
    
    # Deduce house styles
    houses[2]['house_style'] = 'victorian'
    houses[4]['house_style'] = 'modern'
    houses[0]['house_style'] = 'mediterranean'
    houses[5]['house_style'] = 'ranch'
    
    # Prepare the output structure
    header = ["House", "Name", "Pet", "HouseStyle", "Birthday"]
    rows = []
    for i, house in enumerate(houses):
        rows.append([str(i+1), house['name'], house['pet'], house['house_style'], house['birthday']])
    
    solution = {"solution": {"header": header, "rows": rows}}
    
    # Output as JSON
    print(json.dumps(solution))

if __name__ == "__main__":
    main()