import json

def main():
    # Initialize houses with empty attributes
    houses = [{} for _ in range(4)]
    attributes = ['Name', 'House Style', 'Hair Color', 'Child', 'Book Genre']
    for i in range(4):
        for attr in attributes:
            houses[i][attr] = None

    # Fixed assignments from clues
    houses[1]['Name'] = 'Eric'
    houses[1]['Hair Color'] = 'black'
    houses[1]['Child'] = 'Fred'  # Deduced: only remaining child

    houses[2]['House Style'] = 'craftsman'  # Clue 1

    houses[3]['Hair Color'] = 'brown'  # Clue 3
    houses[3]['Child'] = 'Samantha'  # Clue 4

    # House 4 must be Alice
    houses[3]['Name'] = 'Alice'
    houses[3]['House Style'] = 'colonial'  # Clue 8
    houses[3]['Book Genre'] = 'romance'  # Clue 2

    # House 1 must be Arnold (since assigning Peter leads to contradiction)
    houses[0]['Name'] = 'Arnold'
    houses[0]['Hair Color'] = 'red'  # Clue 7
    houses[0]['Child'] = 'Meredith'  # Clue 11
    houses[0]['Book Genre'] = 'science fiction'  # Clue 13

    # House 3 must be Peter
    houses[2]['Name'] = 'Peter'
    houses[2]['Child'] = 'Bella'  # Clue 6
    houses[2]['Book Genre'] = 'fantasy'  # Clue 10

    # Assign house styles: House 2 (index1) is ranch, House 1 (index0) is Victorian
    houses[1]['House Style'] = 'ranch'  # Clue 5: ranch right of red hair (House 1)
    houses[0]['House Style'] = 'victorian'  # Only remaining style

    # Assign book genre for House 2 (index1): mystery
    houses[1]['Book Genre'] = 'mystery'  # Only remaining genre

    # Assign hair color for House 3 (index2): blonde
    houses[2]['Hair Color'] = 'blonde'  # Only remaining hair color

    # Prepare the solution in the required JSON format
    header = ["House"] + attributes
    rows = []
    for i in range(4):
        row = [str(i+1)]
        for attr in attributes:
            row.append(houses[i][attr])
        rows.append(row)

    solution = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution))

if __name__ == "__main__":
    main()