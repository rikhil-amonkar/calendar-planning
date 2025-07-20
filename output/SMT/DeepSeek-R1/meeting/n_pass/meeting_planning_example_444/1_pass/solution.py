from z3 import *

def main():
    # Travel time matrix
    travel_time = {
        'FD': {'RH': 10, 'SD': 31, 'NB': 7, 'TC': 23, 'GG': 23},
        'RH': {'FD': 11, 'SD': 23, 'NB': 5, 'TC': 21, 'GG': 21},
        'SD': {'FD': 30, 'RH': 24, 'NB': 29, 'TC': 17, 'GG': 11},
        'NB': {'FD': 8, 'RH': 4, 'SD': 27, 'TC': 22, 'GG': 22},
        'TC': {'FD': 20, 'RH': 18, 'SD': 17, 'NB': 20, 'GG': 11},
        'GG': {'FD': 26, 'RH': 19, 'SD': 10, 'NB': 24, 'TC': 13}
    }
    
    # Friends' data: name, location, duration, available start (minutes from 9:00), available end
    friends = [
        ('Patricia', 'SD', 60, 15, 780),    # 9:15 AM to 10:00 PM
        ('Ronald', 'RH', 105, 285, 495),     # 1:45 PM to 5:15 PM
        ('Laura', 'NB', 15, 210, 225),       # 12:30 PM to 12:45 PM
        ('Emily', 'TC', 60, 435, 570),       # 4:15 PM to 6:30 PM
        ('Mary', 'GG', 60, 360, 450)         # 3:00 PM to 4:30 PM
    ]
    
    n = len(friends)
    s = Solver()
    
    # Variables: for each friend, whether we attend, start time, and position in the sequence
    attend = [Bool(f"attend_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    position = [Int(f"position_{i}") for i in range(n)]
    
    # End time is start time plus duration
    for i, (name, loc, dur, avail_start, avail_end) in enumerate(friends):
        s.add(end[i] == start[i] + dur)
    
    # Constraints for each friend
    for i, (name, loc, dur, avail_start, avail_end) in enumerate(friends):
        # If attending, the meeting must be within the availability window
        s.add(Implies(attend[i], And(start[i] >= avail_start, end[i] <= avail_end)))
        # If attending, the start time must be at least the travel time from FD to the location
        s.add(Implies(attend[i], start[i] >= travel_time['FD'][loc]))
        # Position must be between 0 and n-1 if attending, or -1 if not
        s.add(Implies(attend[i], And(position[i] >= 0, position[i] < n)))
        s.add(Implies(Not(attend[i]), position[i] == -1))
    
    # If both friends i and j are attended, their positions must be distinct
    for i in range(n):
        for j in range(i+1, n):
            s.add(Implies(And(attend[i], attend[j]), position[i] != position[j]))
    
    # For each pair of friends, if both are attended and i has a lower position than j, 
    # then the start of j must be at least end of i plus travel time from i's location to j's location
    for i in range(n):
        for j in range(n):
            if i != j:
                # If both are attended and position i < position j, then start_j >= end_i + travel(i_loc, j_loc)
                cond = And(attend[i], attend[j], position[i] < position[j])
                loc_i = friends[i][1]
                loc_j = friends[j][1]
                travel_ij = travel_time[loc_i][loc_j]
                s.add(Implies(cond, start[j] >= end[i] + travel_ij))
    
    # Maximize the number of attended meetings
    obj = Sum([If(attend[i], 1, 0) for i in range(n)])
    s.maximize(obj)
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        schedule = []
        for i, (name, loc, dur, avail_start, avail_end) in enumerate(friends):
            if model.evaluate(attend[i]):
                start_val = model.evaluate(start[i]).as_long()
                end_val = model.evaluate(end[i]).as_long()
                # Convert minutes to time string
                start_hour = 9 + start_val // 60
                start_minute = start_val % 60
                end_hour = 9 + end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                schedule.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort schedule by start time
        schedule.sort(key=lambda x: x['start_time'])
        print('SOLUTION:')
        print(f'{{"itinerary": {schedule}}}')
    else:
        print("No solution found")

if __name__ == '__main__':
    main()