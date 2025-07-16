from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations and their indices
    locations = {
        'Sunset District': 0,
        'Russian Hill': 1,
        'Chinatown': 2,
        'Presidio': 3,
        'Fisherman\'s Wharf': 4
    }
    
    # Travel times matrix (in minutes)
    travel_times = [
        [0, 24, 30, 16, 29],    # Sunset District to others
        [23, 0, 9, 14, 7],      # Russian Hill to others
        [29, 7, 0, 19, 8],       # Chinatown to others
        [15, 14, 21, 0, 19],     # Presidio to others
        [27, 7, 12, 17, 0]       # Fisherman's Wharf to others
    ]

    # Friends' data: name, location, start time (minutes since 9:00AM), end time, min duration
    friends = [
        ('William', locations['Russian Hill'], 6*60 + 30 - 9*60, 8*60 + 45 - 9*60, 105),
        ('Michelle', locations['Chinatown'], 8*60 + 15 - 9*60, 14*60 - 9*60, 15),
        ('George', locations['Presidio'], 10*60 + 30 - 9*60, 18*60 + 45 - 9*60, 30),
        ('Robert', locations['Fisherman\'s Wharf'], 0, 1*60 + 45, 30)
    ]
    
    # Variables for each friend: start time (minutes since 9:00AM), end time, and a flag indicating if met
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    met_vars = [Bool(f'met_{name}') for name, _, _, _, _ in friends]

    # Base constraints for each friend
    for i, (name, loc, friend_start, friend_end, min_duration) in enumerate(friends):
        # If meeting the friend, the meeting must be within their window and last at least min_duration
        s.add(Implies(met_vars[i], And(
            start_vars[i] >= friend_start,
            end_vars[i] <= friend_end,
            end_vars[i] == start_vars[i] + min_duration
        )))
        
        # If not meeting the friend, set start and end times to 0
        s.add(Implies(Not(met_vars[i]), And(
            start_vars[i] == 0,
            end_vars[i] == 0
        )))

    # Ordering constraints to ensure travel times are respected
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            # Ensure meetings don't overlap and have enough travel time between them
            s.add(Implies(And(met_vars[i], met_vars[j]),
                Or(
                    end_vars[i] + travel_times[friends[i][1]][friends[j][1]] <= start_vars[j],
                    end_vars[j] + travel_times[friends[j][1]][friends[i][1]] <= start_vars[i]
                )))

    # Maximize the number of friends met
    s.maximize(Sum([If(met_vars[i], 1, 0) for i in range(len(friends))]))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        total_met = 0
        schedule = []
        for i, (name, loc, friend_start, friend_end, min_duration) in enumerate(friends):
            if m.evaluate(met_vars[i]):
                start = m.evaluate(start_vars[i]).as_long()
                end = m.evaluate(end_vars[i]).as_long()
                start_time = f"{9 + start // 60}:{start % 60:02d}"
                end_time = f"{9 + end // 60}:{end % 60:02d}"
                print(f"Meet {name} at {list(locations.keys())[loc]} from {start_time} to {end_time}")
                total_met += 1
                schedule.append((start, end, loc, name))
            else:
                print(f"Cannot meet {name}")
        print(f"Total friends met: {total_met}")
        
        # Print the schedule in chronological order
        schedule.sort()
        print("\nSchedule in order:")
        prev_end = 0
        prev_loc = locations['Sunset District']
        for start, end, loc, name in schedule:
            travel = travel_times[prev_loc][loc]
            travel_start = max(prev_end, start - travel)
            print(f"Travel from {list(locations.keys())[prev_loc]} to {list(locations.keys())[loc]} at {9 + travel_start // 60}:{travel_start % 60:02d} (takes {travel} mins)")
            print(f"Meet {name} from {9 + start // 60}:{start % 60:02d} to {9 + end // 60}:{end % 60:02d}")
            prev_end = end
            prev_loc = loc
    else:
        print("No feasible schedule found.")

solve_scheduling()