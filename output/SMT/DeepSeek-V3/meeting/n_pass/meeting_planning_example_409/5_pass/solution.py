from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations and their indices
    locations = {
        'Fisherman\'s Wharf': 0,
        'Bayview': 1,
        'Golden Gate Park': 2,
        'Nob Hill': 3,
        'Marina District': 4,
        'Embarcadero': 5
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 26, 25, 11, 9, 8],       # Fisherman's Wharf
        [25, 0, 22, 20, 25, 19],     # Bayview
        [24, 23, 0, 20, 16, 25],     # Golden Gate Park
        [11, 19, 17, 0, 11, 9],      # Nob Hill
        [10, 27, 18, 12, 0, 14],     # Marina District
        [6, 21, 25, 10, 12, 0]       # Embarcadero
    ]

    # Friend data: name, location, start time (minutes from 9:00AM), end time, min duration
    friends = [
        ('Thomas', 'Bayview', 390, 510, 120),      # 3:30PM-6:30PM (from 9:00AM)
        ('Stephanie', 'Golden Gate Park', 570, 645, 30),  # 6:30PM-9:45PM
        ('Laura', 'Nob Hill', -15, 435, 30),       # 8:45AM-4:15PM
        ('Betty', 'Marina District', 585, 645, 45),  # 6:45PM-9:45PM
        ('Patricia', 'Embarcadero', 510, 780, 45)   # 5:30PM-10:00PM
    ]

    # Variables for arrival and departure times at each location
    arrival = [Int(f'arrival_{loc}') for loc in locations.keys()]
    departure = [Int(f'departure_{loc}') for loc in locations.keys()]

    # Boolean variables indicating whether we meet each friend
    meet_friends = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]

    # Initial constraints: start at Fisherman's Wharf at 9:00AM (time 0)
    s.add(arrival[locations['Fisherman\'s Wharf']] == 0)
    s.add(departure[locations['Fisherman\'s Wharf']] >= 0)

    # Constraints for each friend
    for i, (name, loc, start, end, min_dur) in enumerate(friends):
        loc_idx = locations[loc]
        # If we meet the friend, arrival and departure must be within their window
        s.add(Implies(meet_friends[i], arrival[loc_idx] >= start))
        s.add(Implies(meet_friends[i], departure[loc_idx] <= end))
        s.add(Implies(meet_friends[i], departure[loc_idx] - arrival[loc_idx] >= min_dur))
        # If we don't meet the friend, arrival/departure must be -1
        s.add(Implies(Not(meet_friends[i]), arrival[loc_idx] == -1))
        s.add(Implies(Not(meet_friends[i]), departure[loc_idx] == -1))

    # Path constraints: ensure travel times between visited locations
    for i in range(len(locations)):
        for j in range(len(locations)):
            if i != j:
                s.add(Implies(And(arrival[i] != -1, arrival[j] != -1),
                            arrival[j] >= departure[i] + travel_times[i][j]))

    # Objective: maximize the number of friends met
    s.maximize(Sum([If(meet_friends[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        total_friends_met = 0
        
        # Get all visited locations with their times
        visited = []
        for loc, idx in locations.items():
            arr = m.evaluate(arrival[idx])
            dep = m.evaluate(departure[idx])
            if arr.as_long() != -1:
                visited.append((loc, arr.as_long(), dep.as_long()))
        
        # Sort by arrival time
        visited.sort(key=lambda x: x[1])
        
        # Print schedule
        for loc, arr, dep in visited:
            # Convert minutes to time format (from 9:00AM base)
            start_h = 9 + arr // 60
            start_m = arr % 60
            end_h = 9 + dep // 60
            end_m = dep % 60
            
            # Handle hour overflow (e.g., 25:30 becomes 1:30 AM next day)
            start_h = start_h % 24
            end_h = end_h % 24
            
            print(f"{start_h}:{start_m:02d}-{end_h}:{end_m:02d} at {loc}")
            
            # Check which friends were met here
            for i, (name, floc, _, _, _) in enumerate(friends):
                if floc == loc and is_true(m.evaluate(meet_friends[i])):
                    print(f"  - Met with {name}")
                    total_friends_met += 1
        
        print(f"\nTotal friends met: {total_friends_met}")
    else:
        print("No feasible schedule found.")

solve_scheduling()