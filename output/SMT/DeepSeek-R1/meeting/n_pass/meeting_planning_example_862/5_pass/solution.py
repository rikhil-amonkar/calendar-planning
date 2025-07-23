from z3 import *
import json

def main():
    friends = [
        ("Laura", 1, 870, 975, 75),   # Alamo Square: 2:30PM to 4:15PM
        ("Brian", 2, 615, 1020, 30),  # Presidio: 10:15AM to 5:00PM
        ("Karen", 3, 1080, 1215, 90), # Russian Hill: 6:00PM to 8:15PM
        ("Stephanie", 4, 615, 960, 75), # North Beach: 10:15AM to 4:00PM
        ("Helen", 5, 690, 1305, 120), # Golden Gate Park: 11:30AM to 9:45PM
        ("Sandra", 6, 480, 915, 30),  # Richmond District: 8:00AM to 3:15PM
        ("Mary", 7, 1005, 1125, 120), # Embarcadero: 4:45PM to 6:45PM
        ("Deborah", 8, 1140, 1245, 105), # Financial District: 7:00PM to 8:45PM
        ("Elizabeth", 9, 510, 795, 105)  # Marina District: 8:30AM to 1:15PM
    ]
    
    travel_matrix = [
        [0, 11, 25, 15, 17, 17, 20, 19, 15, 19],
        [10, 0, 17, 13, 15, 9, 11, 16, 17, 15],
        [26, 19, 0, 14, 18, 12, 7, 20, 23, 11],
        [16, 15, 14, 0, 5, 21, 14, 8, 11, 7],
        [18, 16, 17, 4, 0, 22, 18, 6, 8, 9],
        [17, 9, 11, 19, 23, 0, 7, 25, 26, 16],
        [20, 13, 7, 13, 17, 9, 0, 19, 22, 9],
        [20, 19, 20, 8, 5, 25, 21, 0, 5, 12],
        [17, 17, 22, 11, 7, 23, 21, 4, 0, 15],
        [20, 15, 10, 8, 11, 18, 11, 14, 17, 0]
    ]
    
    n = len(friends)
    opt = Optimize()
    
    scheduled = [Bool(f'scheduled_{i}') for i in range(n)]
    start_time = [Int(f'start_{i}') for i in range(n)]
    end_time = [Int(f'end_{i}') for i in range(n)]
    position = [Int(f'position_{i}') for i in range(n)]
    arrival_time = [Int(f'arrival_{i}') for i in range(n)]
    
    m = Int('m')
    opt.add(m == Sum([If(scheduled[i], 1, 0) for i in range(n)]))
    
    for i in range(n):
        name, loc_idx, avail_start, avail_end, min_dur = friends[i]
        opt.add(If(scheduled[i],
                   And(position[i] >= 1, position[i] <= n,
                       start_time[i] >= avail_start,
                       end_time[i] == start_time[i] + min_dur,
                       end_time[i] <= avail_end,
                       start_time[i] <= avail_end - min_dur),
                   And(position[i] == 0, start_time[i] == 0, end_time[i] == 0)))
    
    # Ensure positions are unique and contiguous
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(scheduled[i], scheduled[j]), position[i] != position[j]))
    
    for k in range(1, n+1):
        count = Sum([If(And(scheduled[i], position[i] == k), 1, 0) for i in range(n)])
        opt.add(count == If(k <= m, 1, 0))
    
    # Travel constraints
    for i in range(n):
        loc_i = friends[i][1]
        # First meeting: from Mission District (location 0)
        opt.add(Implies(And(scheduled[i], position[i] == 1),
                        arrival_time[i] == 540 + travel_matrix[0][loc_i]))
        
        # For meetings after the first
        for j in range(n):
            if i == j:
                continue
            loc_j = friends[j][1]
            opt.add(Implies(And(scheduled[i], scheduled[j], position[j] == position[i] - 1),
                            arrival_time[i] == end_time[j] + travel_matrix[loc_j][loc_i]))
        
        # Meeting must start after arrival
        opt.add(Implies(scheduled[i], start_time[i] >= arrival_time[i]))
    
    opt.maximize(m)
    
    if opt.check() == sat:
        model = opt.model()
        num_scheduled = model.eval(m).as_long()
        meetings = []
        for i in range(n):
            if model.eval(scheduled[i]):
                start_val = model.eval(start_time[i]).as_long()
                end_val = model.eval(end_time[i]).as_long()
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                meetings.append({
                    "person": friends[i][0],
                    "start": start_val,
                    "start_str": start_str,
                    "end_str": end_str,
                    "position": model.eval(position[i]).as_long()
                })
        # Sort by position to get chronological order
        meetings_sorted = sorted(meetings, key=lambda x: x['position'])
        itinerary = []
        for meet in meetings_sorted:
            itinerary.append({
                "action": "meet",
                "person": meet['person'],
                "start_time": meet['start_str'],
                "end_time": meet['end_str']
            })
        print('SOLUTION:')
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('SOLUTION:')
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()