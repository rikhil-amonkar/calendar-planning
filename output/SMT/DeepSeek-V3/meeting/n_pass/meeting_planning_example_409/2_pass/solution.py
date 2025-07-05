from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations
    locations = ['Fisherman\'s Wharf', 'Bayview', 'Golden Gate Park', 'Nob Hill', 'Marina District', 'Embarcadero']
    loc_to_idx = {loc: idx for idx, loc in enumerate(locations)}
    idx_to_loc = {idx: loc for idx, loc in enumerate(locations)}

    # Friends' data: name, location, start, end, min_duration
    friends = [
        ('Thomas', 'Bayview', 390, 570, 120),  # 3:30 PM to 6:30 PM
        ('Stephanie', 'Golden Gate Park', 585, 765, 30),  # 6:30 PM to 9:45 PM
        ('Laura', 'Nob Hill', 0, 435, 30),  # 8:45 AM to 4:15 PM (adjusted to start at 9:00 AM)
        ('Betty', 'Marina District', 585, 765, 45),  # 6:45 PM to 9:45 PM
        ('Patricia', 'Embarcadero', 510, 780, 45)  # 5:30 PM to 10:00 PM
    ]

    # Travel times: matrix [from][to] -> time
    travel = [[0]*len(locations) for _ in range(len(locations))]
    for (f, t), time in {
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Marina District'): 25,
        ('Bayview', 'Embarcadero'): 19,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Nob Hill', 'Fisherman\'s Wharf'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Embarcadero'): 14,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Marina District'): 12,
    }.items():
        travel[loc_to_idx[f]][loc_to_idx[t]] = time

    # Variables
    num_friends = len(friends)
    start = [Int(f'start_{i}') for i in range(num_friends)]
    end = [Int(f'end_{i}') for i in range(num_friends)]
    position = [Int(f'position_{i}') for i in range(num_friends)]
    # Ensure all positions are distinct and between 0 and num_friends-1
    s.add(Distinct(position))
    for i in range(num_friends):
        s.add(position[i] >= 0, position[i] < num_friends)

    # Constraints for each friend
    for i in range(num_friends):
        name, loc, friend_start, friend_end, min_dur = friends[i]
        loc_idx = loc_to_idx[loc]
        # Start and end times are within friend's window and duration is met
        s.add(start[i] >= friend_start)
        s.add(end[i] <= friend_end)
        s.add(end[i] - start[i] >= min_dur)

    # Start at Fisherman's Wharf at time 0
    current_loc = loc_to_idx['Fisherman\'s Wharf']
    current_time = 0

    # Constraints for sequencing and travel times
    for i in range(num_friends):
        for j in range(num_friends):
            if i != j:
                # If friend i is met before friend j in the sequence, then friend j's start time >= friend i's end time + travel time
                i_loc = loc_to_idx[friends[i][1]]
                j_loc = loc_to_idx[friends[j][1]]
                travel_time = travel[i_loc][j_loc]
                s.add(Implies(position[i] < position[j],
                              start[j] >= end[i] + travel_time))

    # Initial travel from Fisherman's Wharf to first friend's location
    for i in range(num_friends):
        loc = friends[i][1]
        loc_idx = loc_to_idx[loc]
        travel_time = travel[current_loc][loc_idx]
        s.add(Implies(position[i] == 0,
                      start[i] >= current_time + travel_time))

    # Objective: minimize the total time spent (optional)
    # s.minimize(end[-1])

    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled = []
        for i in range(num_friends):
            name = friends[i][0]
            loc = friends[i][1]
            st = m[start[i]].as_long()
            en = m[end[i]].as_long()
            pos = m[position[i]].as_long()
            scheduled.append((pos, name, loc, st, en))
        scheduled.sort()
        for pos, name, loc, st, en in scheduled:
            st_time = f"{9 + st // 60}:{st % 60:02d}"
            en_time = f"{9 + en // 60}:{en % 60:02d}"
            print(f"Meet {name} at {loc} from {st_time} to {en_time}")
    else:
        print("No feasible schedule found.")

solve_scheduling()