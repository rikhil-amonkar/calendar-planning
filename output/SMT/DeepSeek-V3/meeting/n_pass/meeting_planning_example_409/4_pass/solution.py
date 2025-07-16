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
        [25, 0, 22, 20, 25, 19],      # Bayview
        [24, 23, 0, 20, 16, 25],      # Golden Gate Park
        [11, 19, 17, 0, 11, 9],       # Nob Hill
        [10, 27, 18, 12, 0, 14],      # Marina District
        [6, 21, 25, 10, 12, 0]        # Embarcadero
    ]

    # Friend data: name, location, start time (minutes from midnight), end time, min duration
    friends = [
        ('Thomas', 'Bayview', 15*60 + 30, 18*60 + 30, 120),      # 3:30PM-6:30PM
        ('Stephanie', 'Golden Gate Park', 18*60 + 30, 21*60 + 45, 30),  # 6:30PM-9:45PM
        ('Laura', 'Nob Hill', 8*60 + 45, 16*60 + 15, 30),       # 8:45AM-4:15PM
        ('Betty', 'Marina District', 18*60 + 45, 21*60 + 45, 45),  # 6:45PM-9:45PM
        ('Patricia', 'Embarcadero', 17*60 + 30, 22*60, 45)       # 5:30PM-10:00PM
    ]

    # Variables for arrival and departure times at each location (in minutes from midnight)
    arrival = [Int(f'arrival_{loc}') for loc in locations.keys()]
    departure = [Int(f'departure_{loc}') for loc in locations.keys()]

    # Boolean variables indicating whether we meet each friend
    meet_friends = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]

    # Initial constraints: start at Fisherman's Wharf at 9:00AM (540 minutes from midnight)
    s.add(arrival[locations['Fisherman\'s Wharf']] == 9*60)
    s.add(departure[locations['Fisherman\'s Wharf']] >= 9*60)

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

    # Additional constraints to prevent visiting same location multiple times
    for i in range(len(locations)):
        s.add(Or(arrival[i] == -1, arrival[i] >= 0))

    # Objective: maximize the number of friends met
    s.maximize(Sum([If(meet_friends[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        total_friends_met = 0
        
        # Sort visited locations by arrival time
        visited = []
        for loc, idx in locations.items():
            arr = m.evaluate(arrival[idx])
            if arr.as_long() != -1:
                visited.append((loc, arr.as_long(), m.evaluate(departure[idx]).as_long()))
        
        visited.sort(key=lambda x: x[1])
        
        for loc, arr, dep in visited:
            # Convert minutes to time format
            start_h = arr // 60
            start_m = arr % 60
            end_h = dep // 60
            end_m = dep % 60
            print(f"At {loc} from {start_h}:{start_m:02d} to {end_h}:{end_m:02d}")
            
            # Check which friend was met here
            for i, (name, floc, _, _, _) in enumerate(friends):
                if floc == loc and is_true(m.evaluate(meet_friends[i])):
                    print(f"  - Met {name}")
                    total_friends_met += 1
        
        print(f"\nTotal friends met: {total_friends_met}")
    else:
        print("No feasible schedule found.")

solve_scheduling()