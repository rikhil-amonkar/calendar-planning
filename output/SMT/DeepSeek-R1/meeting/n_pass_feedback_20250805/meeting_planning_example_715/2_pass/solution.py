from z3 import *

def main():
    # Data setup
    friends = ["Amanda", "Melissa", "Jeffrey", "Matthew", "Nancy", "Karen", "Robert", "Joseph"]
    locations = [
        "Marina District", 
        "The Castro", 
        "Fisherman's Wharf", 
        "Bayview", 
        "Pacific Heights", 
        "Mission District", 
        "Alamo Square", 
        "Golden Gate Park"
    ]
    
    # Travel time from Presidio to each friend's location
    presidio_to = [11, 21, 19, 31, 11, 26, 19, 12]
    
    # Travel time matrix between friends (from i to j)
    travel = [
        [0, 22, 10, 27, 7, 20, 15, 18],
        [21, 0, 24, 19, 16, 7, 8, 11],
        [9, 27, 0, 26, 12, 22, 21, 25],
        [27, 19, 25, 0, 23, 13, 16, 22],
        [6, 16, 13, 22, 0, 15, 10, 15],
        [19, 7, 22, 14, 16, 0, 11, 17],
        [15, 8, 19, 16, 10, 10, 0, 9],
        [16, 13, 24, 23, 16, 17, 9, 0]
    ]
    
    # Availability windows in minutes (start, end)
    windows = [
        (14*60+45, 19*60+30),   # Amanda: 2:45PM to 7:30PM
        (9*60+30, 17*60),        # Melissa: 9:30AM to 5:00PM
        (12*60+45, 18*60+45),    # Jeffrey: 12:45PM to 6:45PM
        (10*60+15, 13*60+15),    # Matthew: 10:15AM to 1:15PM
        (17*60, 21*60+30),       # Nancy: 5:00PM to 9:30PM
        (17*60+30, 20*60+30),    # Karen: 5:30PM to 8:30PM
        (11*60+15, 17*60+30),    # Robert: 11:15AM to 5:30PM
        (8*60+30, 21*60+15)      # Joseph: 8:30AM to 9:15PM
    ]
    
    # Minimum meeting durations in minutes
    min_durations = [105, 30, 120, 30, 105, 105, 120, 105]
    
    # Initialize Z3 variables
    meet = [Bool(f"meet_{i}") for i in range(8)]
    p = [Int(f"p_{i}") for i in range(8)]  # Position in the sequence
    start = [Int(f"start_{i}") for i in range(8)]
    
    # Initialize solver and optimizer
    opt = Optimize()
    
    # Add constraints for each friend
    for i in range(8):
        # If meeting the friend, the meeting must fit within their window
        opt.add(Implies(meet[i], And(start[i] >= windows[i][0], start[i] + min_durations[i] <= windows[i][1])))
        # If meeting the friend, their position must be between 0 and 7
        opt.add(Implies(meet[i], And(p[i] >= 0, p[i] < 8)))
    
    # Travel from start (Presidio) to the first meeting
    for i in range(8):
        opt.add(Implies(And(meet[i], p[i] == 0), start[i] >= 9*60 + presidio_to[i]))
    
    # Distinct positions for met friends
    for i in range(8):
        for j in range(i+1, 8):
            opt.add(Implies(And(meet[i], meet[j]), p[i] != p[j]))
    
    # Consecutive meetings must account for travel time
    for i in range(8):
        for j in range(8):
            if i != j:
                opt.add(Implies(
                    And(meet[i], meet[j], p[i] >= 1, p[j] == p[i] - 1),
                    start[i] >= start[j] + min_durations[j] + travel[j][i]
                ))
    
    # Every non-first meeting must have a predecessor
    for i in range(8):
        other_js = [j for j in range(8) if j != i]
        opt.add(Implies(
            And(meet[i], p[i] >= 1),
            Or([And(meet[j], p[j] == p[i] - 1) for j in other_js])
        ))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(8)])
    opt.maximize(total_meetings)
    
    # Solve the model
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(8):
            if m.evaluate(meet[i]):
                start_val = m.evaluate(start[i])
                start_min = start_val.as_long() if is_int_value(start_val) else int(str(start_val))
                end_min = start_min + min_durations[i]
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort meetings by start time (fixed syntax error)
        itinerary.sort(key=lambda x: int(x['start_time'].split(':')[0]) * 60 + int(x['start_time'].split(':')[1]))
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()