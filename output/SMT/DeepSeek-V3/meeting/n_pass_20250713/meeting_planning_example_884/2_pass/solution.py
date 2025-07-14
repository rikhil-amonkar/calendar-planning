from z3 import *

def solve_scheduling():
    # Initialize solver
    opt = Optimize()

    # Convert all times to minutes since midnight
    def time_to_minutes(h, m):
        return h * 60 + m

    friends_data = [
        ("Robert", "Chinatown", time_to_minutes(7, 45), time_to_minutes(17, 30), 120),
        ("David", "Sunset District", time_to_minutes(12, 30), time_to_minutes(19, 45), 45),
        ("Matthew", "Alamo Square", time_to_minutes(8, 45), time_to_minutes(13, 45), 90),
        ("Jessica", "Financial District", time_to_minutes(9, 30), time_to_minutes(18, 45), 45),
        ("Melissa", "North Beach", time_to_minutes(7, 15), time_to_minutes(16, 45), 45),
        ("Mark", "Embarcadero", time_to_minutes(15, 15), time_to_minutes(17, 0), 45),
        ("Deborah", "Presidio", time_to_minutes(19, 0), time_to_minutes(19, 45), 45),
        ("Karen", "Golden Gate Park", time_to_minutes(19, 30), time_to_minutes(22, 0), 120),
        ("Laura", "Bayview", time_to_minutes(21, 15), time_to_minutes(22, 15), 15)
    ]

    travel_times = {
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Bayview"): 27,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 20,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Bayview"): 22,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Bayview"): 16,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Bayview"): 19,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Bayview"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Bayview"): 23,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Golden Gate Park"): 22,
    }

    # Variables for each friend: start and end times, and a flag to indicate if the friend is met
    friend_vars = []
    for name, loc, avail_from, avail_to, min_dur in friends_data:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        met = Bool(f'met_{name}')
        opt.add(Implies(met, start >= avail_from))
        opt.add(Implies(met, end <= avail_to))
        opt.add(Implies(met, end == start + min_dur))
        friend_vars.append((name, loc, start, end, min_dur, met))

    # Starting point: Richmond District at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = "Richmond District"

    # Ensure exactly 8 friends are met
    opt.add(Sum([If(met, 1, 0) for (_, _, _, _, _, met) in friend_vars]) == 8

    # Sequence constraints: order of meetings and travel times
    # We'll use a list to represent the order and enforce constraints
    order = [Int(f'order_{i}') for i in range(8)]
    opt.add(Distinct(order))
    for i in range(8):
        opt.add(order[i] >= 0)
        opt.add(order[i] < len(friend_vars))

    # Enforce that the selected friends are met
    for i in range(8):
        for j, (_, _, _, _, _, met) in enumerate(friend_vars):
            opt.add(Implies(order[i] == j, met))

    # Enforce travel times between consecutive meetings
    for i in range(7):
        prev_idx = order[i]
        next_idx = order[i + 1]
        prev_name, prev_loc, prev_start, prev_end, prev_dur, _ = friend_vars[prev_idx]
        next_name, next_loc, next_start, next_end, next_dur, _ = friend_vars[next_idx]
        travel_time = travel_times.get((prev_loc, next_loc), 0)
        opt.add(next_start >= prev_end + travel_time)

    # The first meeting must start after arriving at Richmond District at 9:00 AM
    first_idx = order[0]
    first_name, first_loc, first_start, first_end, first_dur, _ = friend_vars[first_idx]
    travel_time_first = travel_times.get((current_loc, first_loc), 0)
    opt.add(first_start >= current_time + travel_time_first)

    # Maximize the total meeting time (optional)
    total_meeting_time = Sum([If(met, min_dur, 0) for (_, _, _, _, min_dur, met) in friend_vars])
    opt.maximize(total_meeting_time)

    if opt.check() == sat:
        m = opt.model()
        schedule = []
        for name, loc, start, end, min_dur, met in friend_vars:
            if m.evaluate(met):
                start_val = m.evaluate(start).as_long()
                end_val = m.evaluate(end).as_long()
                schedule.append((name, loc, start_val, end_val))
        # Sort schedule by start time
        schedule.sort(key=lambda x: x[2])
        # Convert minutes back to time strings
        def minutes_to_time(m):
            h = m // 60
            m = m % 60
            return f"{h}:{m:02d}"
        print("SOLUTION:")
        for name, loc, start, end in schedule:
            print(f"Meet {name} at {loc} from {minutes_to_time(start)} to {minutes_to_time(end)}")
    else:
        print("No feasible schedule found.")

# Call the function
solve_scheduling()