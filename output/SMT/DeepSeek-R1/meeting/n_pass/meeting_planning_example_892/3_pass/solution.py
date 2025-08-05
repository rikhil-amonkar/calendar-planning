from z3 import *

def main():
    meetings = [
        {'name': 'Laura', 'loc': 0, 'start_avail': 465, 'end_avail': 795, 'min_dur': 105},
        {'name': 'Charles', 'loc': 1, 'start_avail': 690, 'end_avail': 870, 'min_dur': 45},
        {'name': 'Robert', 'loc': 2, 'start_avail': 1005, 'end_avail': 1260, 'min_dur': 30},
        {'name': 'Karen', 'loc': 3, 'start_avail': 1155, 'end_avail': 1290, 'min_dur': 60},
        {'name': 'Rebecca', 'loc': 4, 'start_avail': 975, 'end_avail': 1230, 'min_dur': 90},
        {'name': 'Margaret', 'loc': 5, 'start_avail': 855, 'end_avail': 1185, 'min_dur': 120},
        {'name': 'Patricia', 'loc': 6, 'start_avail': 870, 'end_avail': 1230, 'min_dur': 45},
        {'name': 'Mark', 'loc': 7, 'start_avail': 840, 'end_avail': 1110, 'min_dur': 105},
        {'name': 'Melissa', 'loc': 8, 'start_avail': 780, 'end_avail': 1185, 'min_dur': 30},
        {'name': 'start', 'loc': None, 'start_avail': 540, 'end_avail': 540, 'min_dur': 0}
    ]
    
    travel_marina = [14, 27, 19, 11, 12, 15, 16, 11, 8]
    
    travel_matrix = [
        [0, 21, 30, 21, 10, 7, 21, 5, 8],
        [19, 0, 23, 25, 20, 19, 19, 22, 23],
        [30, 22, 0, 12, 27, 30, 15, 28, 24],
        [19, 27, 11, 0, 17, 20, 10, 17, 13],
        [9, 19, 24, 14, 0, 6, 13, 8, 5],
        [5, 20, 29, 20, 9, 0, 19, 3, 7],
        [20, 18, 15, 10, 15, 19, 0, 19, 17],
        [6, 25, 27, 18, 7, 6, 18, 0, 4],
        [8, 23, 23, 14, 5, 9, 17, 5, 0]
    ]
    
    n = len(meetings)
    opt = Optimize()
    
    attend = [Bool(f'attend_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    position = [Int(f'position_{i}') for i in range(n)]
    
    # Fix dummy meeting constraints
    opt.add(attend[9] == True)
    opt.add(start[9] == 540)
    opt.add(end[9] == 540)
    opt.add(position[9] == 0)
    
    # Real meetings constraints
    for i in range(9):
        opt.add(Implies(attend[i], 
                     And(start[i] >= meetings[i]['start_avail'],
                         end[i] <= meetings[i]['end_avail'],
                         end[i] - start[i] >= meetings[i]['min_dur'])))
        opt.add(Implies(Not(attend[i]), position[i] == -1))
        opt.add(Implies(attend[i], position[i] >= 0))
    
    max_pos = 9
    # Distinct positions for attended meetings
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(attend[i], attend[j]), position[i] != position[j]))
    
    # Contiguous position constraints
    for k in range(1, max_pos+1):
        # If position k exists, then position k-1 must exist
        cond = Or([And(attend[i], position[i] == k) for i in range(n)])
        then_cond = Or([And(attend[i], position[i] == k-1) for i in range(n)])
        opt.add(Implies(cond, then_cond))
    
    # Travel time function
    def get_travel_time(i, j):
        if i == 9:  # from dummy (Marina) to j
            return travel_marina[meetings[j]['loc']]
        elif j == 9:  # to dummy (Marina) - not needed
            return 0
        else:
            loc_i = meetings[i]['loc']
            loc_j = meetings[j]['loc']
            return travel_matrix[loc_i][loc_j]
    
    # Travel time constraints for consecutive meetings
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            opt.add(Implies(And(attend[i], attend[j], position[j] == position[i] + 1),
                         start[j] >= end[i] + get_travel_time(i, j)))
    
    # Maximize attended meetings
    real_attended = Sum([If(attend[i], 1, 0) for i in range(9)])
    opt.maximize(real_attended)
    
    # Solve and output
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for i in range(9):
            if model.eval(attend[i]):
                start_val = model.eval(start[i]).as_long()
                end_val = model.eval(end[i]).as_long()
                start_str = f"{start_val//60:02d}:{start_val%60:02d}"
                end_str = f"{end_val//60:02d}:{end_val%60:02d}"
                schedule.append({
                    'person': meetings[i]['name'],
                    'start_time': start_str,
                    'end_time': end_str
                })
        # Sort by start time
        schedule_sorted = sorted(schedule, key=lambda x: x['start_time'])
        itinerary = [{"action": "meet", "person": item['person'], 
                      "start_time": item['start_time'], "end_time": item['end_time']} 
                     for item in schedule_sorted]
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()