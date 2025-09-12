from z3 import *
import json

def main():
    # Define the locations and their indices
    locations = [
        'Russian Hill',
        'Marina District',
        'Financial District',
        'Alamo Square',
        'Golden Gate Park',
        'The Castro',
        'Bayview',
        'Sunset District',
        'Haight-Ashbury',
        'Nob Hill'
    ]
    
    # Create a 10x10 travel time matrix
    travel_matrix = [[0] * 10 for _ in range(10)]
    
    # Fill the travel matrix with the given values
    travel_matrix[0][1] = 7
    travel_matrix[0][2] = 11
    travel_matrix[0][3] = 15
    travel_matrix[0][4] = 21
    travel_matrix[0][5] = 21
    travel_matrix[0][6] = 23
    travel_matrix[0][7] = 23
    travel_matrix[0][8] = 17
    travel_matrix[0][9] = 5
    
    travel_matrix[1][0] = 8
    travel_matrix[1][2] = 17
    travel_matrix[1][3] = 15
    travel_matrix[1][4] = 18
    travel_matrix[1][5] = 22
    travel_matrix[1][6] = 27
    travel_matrix[1][7] = 19
    travel_matrix[1][8] = 16
    travel_matrix[1][9] = 12
    
    travel_matrix[2][0] = 11
    travel_matrix[2][1] = 15
    travel_matrix[2][3] = 17
    travel_matrix[2][4] = 23
    travel_matrix[2][5] = 20
    travel_matrix[2][6] = 19
    travel_matrix[2][7] = 30
    travel_matrix[2][8] = 19
    travel_matrix[2][9] = 8
    
    travel_matrix[3][0] = 13
    travel_matrix[3][1] = 15
    travel_matrix[3][2] = 17
    travel_matrix[3][4] = 9
    travel_matrix[3][5] = 8
    travel_matrix[3][6] = 16
    travel_matrix[3][7] = 16
    travel_matrix[3][8] = 5
    travel_matrix[3][9] = 11
    
    travel_matrix[4][0] = 19
    travel_matrix[4][1] = 16
    travel_matrix[4][2] = 26
    travel_matrix[4][3] = 9
    travel_matrix[4][5] = 13
    travel_matrix[4][6] = 23
    travel_matrix[4][7] = 10
    travel_matrix[4][8] = 7
    travel_matrix[4][9] = 20
    
    travel_matrix[5][0] = 18
    travel_matrix[5][1] = 21
    travel_matrix[5][2] = 21
    travel_matrix[5][3] = 8
    travel_matrix[5][4] = 11
    travel_matrix[5][6] = 19
    travel_matrix[5][7] = 17
    travel_matrix[5][8] = 6
    travel_matrix[5][9] = 16
    
    travel_matrix[6][0] = 23
    travel_matrix[6][1] = 27
    travel_matrix[6][2] = 19
    travel_matrix[6][3] = 16
    travel_matrix[6][4] = 22
    travel_matrix[6][5] = 19
    travel_matrix[6][7] = 23
    travel_matrix[6][8] = 19
    travel_matrix[6][9] = 20
    
    travel_matrix[7][0] = 24
    travel_matrix[7][1] = 21
    travel_matrix[7][2] = 30
    travel_matrix[7][3] = 17
    travel_matrix[7][4] = 11
    travel_matrix[7][5] = 17
    travel_matrix[7][6] = 22
    travel_matrix[7][8] = 15
    travel_matrix[7][9] = 27
    
    travel_matrix[8][0] = 17
    travel_matrix[8][1] = 17
    travel_matrix[8][2] = 21
    travel_matrix[8][3] = 5
    travel_matrix[8][4] = 7
    travel_matrix[8][5] = 6
    travel_matrix[8][6] = 18
    travel_matrix[8][7] = 15
    travel_matrix[8][9] = 15
    
    travel_matrix[9][0] = 5
    travel_matrix[9][1] = 11
    travel_matrix[9][2] = 9
    travel_matrix[9][3] = 11
    travel_matrix[9][4] = 17
    travel_matrix[9][5] = 17
    travel_matrix[9][6] = 19
    travel_matrix[9][7] = 24
    travel_matrix[9][8] = 13

    # Function to get travel time between two nodes (0-10)
    def T(i, j):
        map_i = 0 if i in [0, 10] else i
        map_j = 0 if j in [0, 10] else j
        return travel_matrix[map_i][map_j]

    # People data: index 1 to 9
    people = {
        1: {'name': 'Mark', 'location': 1, 'avail_start': 585, 'avail_end': 720, 'min_dur': 90},
        2: {'name': 'Karen', 'location': 2, 'avail_start': 30, 'avail_end': 225, 'min_dur': 90},
        3: {'name': 'Barbara', 'location': 3, 'avail_start': 60, 'avail_end': 630, 'min_dur': 90},
        4: {'name': 'Nancy', 'location': 4, 'avail_start': 465, 'avail_end': 660, 'min_dur': 105},
        5: {'name': 'David', 'location': 5, 'avail_start': 0, 'avail_end': 540, 'min_dur': 120},
        6: {'name': 'Linda', 'location': 6, 'avail_start': 555, 'avail_end': 645, 'min_dur': 45},
        7: {'name': 'Kevin', 'location': 7, 'avail_start': 60, 'avail_end': 525, 'min_dur': 120},
        8: {'name': 'Matthew', 'location': 8, 'avail_start': 75, 'avail_end': 390, 'min_dur': 45},
        9: {'name': 'Andrew', 'location': 9, 'avail_start': 165, 'avail_end': 465, 'min_dur': 105}
    }

    # Create Z3 variables
    meet = [Bool(f'meet_{i}') for i in range(1, 10)]
    start = [Int(f'start_{i}') for i in range(1, 10)]
    end = [Int(f'end_{i}') for i in range(1, 10)]
    before = [[Bool(f'before_{i}_{j}') for j in range(11)] for i in range(11)]

    opt = Optimize()

    # Constraints for each person
    for i in range(1, 10):
        opt.add(Implies(meet[i-1], start[i-1] >= people[i]['avail_start']))
        opt.add(Implies(meet[i-1], end[i-1] <= people[i]['avail_end']))
        opt.add(Implies(meet[i-1], end[i-1] - start[i-1] >= people[i]['min_dur']))

    # Constraints for dummy nodes (0 and 10)
    opt.add(Sum([before[0][j] for j in range(1, 11)]) == 1)
    opt.add(Sum([before[j][0] for j in range(0, 11)]) == 0)
    opt.add(Sum([before[j][10] for j in range(0, 10)]) == 1)
    opt.add(Sum([before[10][j] for j in range(0, 11)]) == 0)

    # Constraints for meeting nodes
    for i in range(1, 10):
        opt.add(Implies(meet[i-1], Sum([before[j][i] for j in range(0, 11) if j != i]) == 1))
        opt.add(Implies(meet[i-1], Sum([before[i][j] for j in range(0, 11) if j != i]) == 1))
        opt.add(Implies(Not(meet[i-1]), And([Not(before[j][i]) for j in range(0, 11) if j != i])))
        opt.add(Implies(Not(meet[i-1]), And([Not(before[i][j]) for j in range(0, 11) if j != i])))

    # Time constraints for consecutive nodes
    for i in range(0, 11):
        for j in range(0, 11):
            if i == j:
                continue
            if i == 0:
                end_i = 0
                selected_i = True
            elif i == 10:
                continue
            else:
                end_i = end[i-1]
                selected_i = meet[i-1]
            if j == 0:
                continue
            elif j == 10:
                selected_j = True
            else:
                start_j = start[j-1]
                selected_j = meet[j-1]
            if i != 10 and j != 0:
                opt.add(Implies(And(selected_i, selected_j, before[i][j]), end_i + T(i, j) <= start_j))

    # Maximize the number of meetings
    opt.maximize(Sum([If(m, 1, 0) for m in meet]))

    # Convert minutes to time string
    def to_time(minutes):
        total_minutes = minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        current = 0
        while current != 10:
            next_node = None
            for j in range(0, 11):
                if j != current and m.eval(before[current][j]):
                    next_node = j
                    break
            if next_node is None:
                break
            if next_node not in (0, 10):
                idx = next_node - 1
                if m.eval(meet[idx]):
                    p = people[next_node]
                    start_val = m.eval(start[idx]).as_long()
                    end_val = m.eval(end[idx]).as_long()
                    itinerary.append({
                        "action": "meet",
                        "location": locations[p['location']],
                        "person": p['name'],
                        "start_time": to_time(start_val),
                        "end_time": to_time(end_val)
                    })
            current = next_node
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()