from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define locations and travel times
    locations = {
        "Golden Gate Park": 0,
        "Haight-Ashbury": 1,
        "Fisherman's Wharf": 2,
        "The Castro": 3,
        "Chinatown": 4,
        "Alamo Square": 5,
        "North Beach": 6,
        "Russian Hill": 7
    }

    travel_time = [
        [0, 7, 24, 13, 23, 10, 24, 19],
        [7, 0, 23, 6, 19, 5, 19, 17],
        [25, 22, 0, 26, 12, 20, 6, 7],
        [11, 6, 24, 0, 20, 8, 20, 18],
        [23, 19, 8, 22, 0, 17, 3, 7],
        [9, 5, 19, 8, 16, 0, 15, 13],
        [22, 18, 5, 22, 6, 16, 0, 4],
        [21, 17, 7, 21, 9, 15, 5, 0]
    ]

    # Friends data: name, location, start, end, min_duration
    friends = [
        ("Carol", "Haight-Ashbury", 1290, 1350, 60),
        ("Laura", "Fisherman's Wharf", 705, 1290, 60),
        ("Karen", "The Castro", 435, 840, 75),
        ("Elizabeth", "Chinatown", 735, 1290, 75),
        ("Deborah", "Alamo Square", 720, 900, 105),
        ("Jason", "North Beach", 885, 1140, 90),
        ("Steven", "Russian Hill", 885, 1110, 120)
    ]

    # Decision variables
    meet = [Bool(f"meet_{i}") for i in range(len(friends))]
    start = [Int(f"start_{i}") for i in range(len(friends))]
    end = [Int(f"end_{i}") for i in range(len(friends))]

    # Initial conditions
    current_time = Int("init_time")
    s.add(current_time == 540)  # 9:00 AM in minutes
    current_loc = Int("init_loc")
    s.add(current_loc == locations["Golden Gate Park"])

    # Meeting constraints
    for i, (name, loc, f_start, f_end, duration) in enumerate(friends):
        loc_idx = locations[loc]
        
        # If meeting this friend
        s.add(Implies(meet[i], And(
            start[i] >= f_start,
            end[i] <= f_end,
            end[i] - start[i] >= duration,
            start[i] >= current_time + travel_time[current_loc][loc_idx]
        )))

        # Update current time and location if meeting
        new_time = Int(f"time_after_{i}")
        new_loc = Int(f"loc_after_{i}")
        s.add(If(meet[i], 
                 And(new_time == end[i], new_loc == loc_idx),
                 And(new_time == current_time, new_loc == current_loc)))
        
        current_time = new_time
        current_loc = new_loc

    # No overlapping meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            s.add(Implies(And(meet[i], meet[j]),
                         Or(end[i] + travel_time[locations[friends[i][1]]][locations[friends[j][1]]] <= start[j],
                            end[j] + travel_time[locations[friends[j][1]]][locations[friends[i][1]]] <= start[i])))

    # Maximize number of friends met
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(len(friends))]))

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        met = [i for i in range(len(friends)) if is_true(m.evaluate(meet[i]))]
        print(f"Total friends met: {len(met)}")
        
        # Get schedule in chronological order
        schedule = []
        for i in met:
            start_val = m.evaluate(start[i]).as_long()
            schedule.append((start_val, i))
        schedule.sort()
        
        # Print schedule
        current_time = 540
        current_loc = locations["Golden Gate Park"]
        for time, i in schedule:
            name, loc, _, _, _ = friends[i]
            loc_idx = locations[loc]
            travel = travel_time[current_loc][loc_idx]
            print(f"Travel: {travel} mins to {loc}")
            print(f"Meet {name} at {time//60}:{time%60:02d} for {m.evaluate(end[i]).as_long() - time} mins")
            current_time = m.evaluate(end[i]).as_long()
            current_loc = loc_idx
    else:
        print("No valid schedule found")

solve_scheduling()