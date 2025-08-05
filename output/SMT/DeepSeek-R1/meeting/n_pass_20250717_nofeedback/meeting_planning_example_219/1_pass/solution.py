from z3 import *

def main():
    meetings = ["Emily", "Barbara", "William"]
    n = len(meetings)
    
    min_durations = [105, 60, 105]  # in minutes
    
    # Times in minutes from 9:00 AM
    available_start = [
        11 * 60 + 45,  # Emily: 11:45 AM
        16 * 60 + 45,  # Barbara: 4:45 PM
        17 * 60 + 15   # William: 5:15 PM
    ]
    available_end = [
        15 * 60 + 15,  # Emily: 3:15 PM
        18 * 60 + 15,  # Barbara: 6:15 PM
        19 * 60 + 0    # William: 7:00 PM
    ]
    
    # Location indices:
    # Castro: 0, Alamo Square:1, Union Square:2, Chinatown:3
    loc_index = [1, 2, 3]  # Emily at Alamo, Barbara at Union, William at Chinatown
    
    # Travel time matrix (from row to column)
    travel = [
        [0, 8, 19, 20],  # from Castro (0) to [0,1,2,3]
        [8, 0, 14, 16],  # from Alamo (1) to [0,1,2,3]
        [19, 15, 0, 7],  # from Union (2) to [0,1,2,3]
        [22, 17, 7, 0]   # from Chinatown (3) to [0,1,2,3]
    ]
    
    s = Optimize()
    
    # Decision variables
    attended = [Bool(f'attended_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    
    # Before matrix: before[i][j] is True if meeting i is before meeting j (both attended)
    before = [[Bool(f'before_{i}_{j}') for j in range(n)] for i in range(n)]
    
    # Constraints for each meeting
    for i in range(n):
        s.add(end[i] == start[i] + min_durations[i])
        s.add(Implies(attended[i], start[i] >= available_start[i]))
        s.add(Implies(attended[i], end[i] <= available_end[i]))
        travel_time_i = travel[0][loc_index[i]]
        s.add(Implies(attended[i], start[i] >= travel_time_i))
    
    # Constraints for ordering and travel between meetings
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            s.add(Implies(And(attended[i], attended[j]), 
                             Or(before[i][j], before[j][i])))
            s.add(Implies(And(attended[i], attended[j]), 
                             Not(And(before[i][j], before[j][i]))))
            loc_i = loc_index[i]
            loc_j = loc_index[j]
            travel_ij = travel[loc_i][loc_j]
            s.add(Implies(And(attended[i], attended[j], before[i][j]), 
                             start[j] >= end[i] + travel_ij))
    
    # Maximize the number of attended meetings
    num_attended = Sum([If(attended[i], 1, 0) for i in range(n)])
    s.maximize(num_attended)
    
    # Solve and extract solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            if m.evaluate(attended[i]):
                start_val = m.evaluate(start[i]).as_long()
                end_val = m.evaluate(end[i]).as_long()
                start_hour = 9 + start_val // 60
                start_minute = start_val % 60
                end_hour = 9 + end_val // 60
                end_minute = end_val % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meetings[i],
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print(result)
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()