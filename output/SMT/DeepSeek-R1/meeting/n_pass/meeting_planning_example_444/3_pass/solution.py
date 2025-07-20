from z3 import *

def main():
    # Corrected travel time matrix based on problem description
    travel_time = {
        'FD': {'RH': 10, 'SD': 30, 'NB': 8, 'TC': 20, 'GG': 26},
        'RH': {'FD': 10, 'SD': 23, 'NB': 5, 'TC': 18, 'GG': 19},
        'SD': {'FD': 30, 'RH': 23, 'NB': 27, 'TC': 17, 'GG': 11},
        'NB': {'FD': 8, 'RH': 5, 'SD': 27, 'TC': 20, 'GG': 24},
        'TC': {'FD': 20, 'RH': 18, 'SD': 17, 'NB': 20, 'GG': 13},
        'GG': {'FD': 26, 'RH': 19, 'SD': 11, 'NB': 24, 'TC': 13}
    }
    
    # Friends' data: name, location, duration, available start (minutes from 9:00), available end
    friends = [
        ('Patricia', 'SD', 60, 15, 780),    # 9:15 AM to 10:00 PM (780 minutes)
        ('Ronald', 'RH', 105, 285, 495),    # 1:45 PM to 5:15 PM (285 to 495 minutes)
        ('Laura', 'NB', 15, 210, 225),      # 12:30 PM to 12:45 PM (210 to 225 minutes)
        ('Emily', 'TC', 60, 435, 570),       # 4:15 PM to 6:30 PM (435 to 570 minutes)
        ('Mary', 'GG', 60, 360, 450)         # 3:00 PM to 4:30 PM (360 to 450 minutes)
    ]
    
    n = len(friends)
    opt = Optimize()
    
    # Variables: for each friend, whether we attend, start time, and position in the sequence
    attend = [Bool(f"attend_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    position = [Int(f"position_{i}") for i in range(n)]
    
    # End time is start time plus duration
    for i, (name, loc, dur, avail_start, avail_end) in enumerate(friends):
        opt.add(end[i] == start[i] + dur)
    
    # Constraints for each friend
    for i, (name, loc, dur, avail_start, avail_end) in enumerate(friends):
        # If attending, meeting must be within availability window
        opt.add(Implies(attend[i], And(start[i] >= avail_start, end[i] <= avail_end)))
        # If attending, start time must account for travel from FD
        opt.add(Implies(attend[i], start[i] >= travel_time['FD'][loc]))
        # Position must be valid if attending
        opt.add(Implies(attend[i], And(position[i] >= 0, position[i] < n)))
        opt.add(Implies(Not(attend[i]), position[i] == -1))
    
    # All attended meetings must have distinct positions
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(attend[i], attend[j]), position[i] != position[j]))
    
    # Travel time constraints between consecutive meetings
    for i in range(n):
        for j in range(n):
            if i != j:
                # If both meetings are attended and i comes before j
                cond = And(attend[i], attend[j], position[i] < position[j])
                loc_i = friends[i][1]
                loc_j = friends[j][1]
                travel_ij = travel_time[loc_i][loc_j]
                opt.add(Implies(cond, start[j] >= end[i] + travel_ij))
    
    # Maximize number of attended meetings
    obj = Sum([If(attend[i], 1, 0) for i in range(n)])
    opt.maximize(obj)
    
    # Solve and output
    if opt.check() == sat:
        model = opt.model()
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
                start_str = f"{start_hour}:{start_minute:02d}"
                end_str = f"{end_hour}:{end_minute:02d}"
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