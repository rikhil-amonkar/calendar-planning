import json

def main():
    houses = [{'name': None, 'style': None} for _ in range(4)]
    
    # Apply fixed constraints
    houses[2]['name'] = 'Eric'     # Eric in third house
    houses[3]['name'] = 'Arnold'   # Arnold in fourth house
    houses[2]['style'] = 'craftsman' # Craftsman style for Eric
    
    # Deduce styles: ranch left of Victorian
    houses[0]['style'] = 'ranch'
    houses[1]['style'] = 'victorian'
    houses[3]['style'] = 'colonial'  # Only style left
    
    # Victorian house is Alice
    houses[1]['name'] = 'Alice'
    # Only name left for first house
    houses[0]['name'] = 'Peter'
    
    # Prepare output
    header = ["House", "Name", "Style"]
    rows = []
    for i in range(4):
        house_number = str(i + 1)
        name = houses[i]['name']
        style = houses[i]['style']
        rows.append([house_number, name, style])
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()