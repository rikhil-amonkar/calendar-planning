from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations and their indices
    locations = {
        'Union Square': 0,
        'Golden Gate Park': 1,
        'Pacific Heights': 2,
        'Presidio': 3,
        'Chinatown': 4,
        'The Castro': 5
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 22, 15, 24, 7, 19],    # Union Square to others
        [22, 0, 16, 11, 23, 13],    # Golden Gate Park to others
        [15, 16, 0, 11, 11, 16],    # Pacific Heights to others
        [24, 11, 11, 0, 21, 21],    # Presidio to others
        [7, 23, 10, 19, 0, 20],      # Chinatown to others
        [19, 11, 16, 20, 20, 0]      # The Castro to others
    ]

    # Friend data: name, location, start time, end time, min duration (in minutes from 9:00 AM)
    friends = [
        ('Andrew', 1, 11*60 + 45, 14*60 + 30, 75),
        ('Sarah', 2, 16*60 + 15, 18*60 + 45, 15),
        ('Nancy', 3, 17*60 + 30, 19*60 + 15, 60),
        ('Rebecca', 4, 9*60 + 45, 21*60 + 30, 90),
        ('Robert', 5, 8*60 + 30, 14*60 + 15, 30)
    ]

    # Variables for each friend: start and end of meeting
    start_vars = []
    end_vars = []
    for i, (name, loc, friend_start, friend_end, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        start_vars.append(start)
        end_vars.append(end)

        # Constraints for meeting
        s.add(start >= friend_start)
        s.add(end <= friend_end)
        s.add(end - start >= min_dur)
        s.add(start >= 0)
        s.add(end >= 0)

    # Initial position is Union Square at time 0 (9:00 AM)
    current_loc = locations['Union Square']
    current_time = 0

    # Ensure all friends are met in order
    for i in range(len(friends)):
        s.add(start_vars[i] >= current_time + travel_times[current_loc][friends[i][1]])
        current_time = end_vars[i]
        current_loc = friends[i][1]

    # No overlapping meetings
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            s.add(Or(end_vars[i] + travel_times[friends[i][1]][friends[j][1]] <= start_vars[j],
                     end_vars[j] + travel_times[friends[j][1]][friends[i][1]] <= start_vars[i]))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        print("Start at Union Square at 9:00 AM")
        current_time = 0
        current_loc = locations['Union Square']
        met_friends = []
        # Determine the order of meetings based on start times
        friend_order = sorted([(i, m.evaluate(start_vars[i]).as_long()) for i in range(len(friends))], key=lambda x: x[1])
        for i, start in friend_order:
            name, loc, _, _, min_dur = friends[i]
            start_time = start
            end_time = m.evaluate(end_vars[i]).as_long()
            travel_time = travel_times[current_loc][loc]
            print(f"Travel from {list(locations.keys())[current_loc]} to {list(locations.keys())[loc]} (takes {travel_time} minutes)")
            print(f"Meet {name} at {list(locations.keys())[loc]} from {start_time//60:02d}:{start_time%60:02d} to {end_time//60:02d}:{end_time%60:02d} (duration: {end_time - start_time} minutes)")
            current_time = end_time
            current_loc = loc
            met_friends.append(name)
        print(f"Total friends met: {len(met_friends)} ({', '.join(met_friends)})")
    else:
        print("No feasible schedule found.")

solve_scheduling()