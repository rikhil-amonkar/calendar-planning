from z3 import *

def main():
    # Build travel_time_dict from provided data
    travel_data = [
        ("Embarcadero", "Bayview", 21),
        ("Embarcadero", "Chinatown", 7),
        ("Embarcadero", "Alamo Square", 19),
        ("Embarcadero", "Nob Hill", 10),
        ("Embarcadero", "Presidio", 20),
        ("Embarcadero", "Union Square", 10),
        ("Embarcadero", "The Castro", 25),
        ("Embarcadero", "North Beach", 5),
        ("Embarcadero", "Fisherman's Wharf", 6),
        ("Embarcadero", "Marina District", 12),
        ("Bayview", "Embarcadero", 19),
        ("Bayview", "Chinatown", 19),
        ("Bayview", "Alamo Square", 16),
        ("Bayview", "Nob Hill", 20),
        ("Bayview", "Presidio", 32),
        ("Bayview", "Union Square", 18),
        ("Bayview", "The Castro", 19),
        ("Bayview", "North Beach", 22),
        ("Bayview", "Fisherman's Wharf", 25),
        ("Bayview", "Marina District", 27),
        ("Chinatown", "Embarcadero", 5),
        ("Chinatown", "Bayview", 20),
        ("Chinatown", "Alamo Square", 17),
        ("Chinatown", "Nob Hill", 9),
        ("Chinatown", "Presidio", 19),
        ("Chinatown", "Union Square", 7),
        ("Chinatown", "The Castro", 22),
        ("Chinatown", "North Beach", 3),
        ("Chinatown", "Fisherman's Wharf", 8),
        ("Chinatown", "Marina District", 12),
        ("Alamo Square", "Embarcadero", 16),
        ("Alamo Square", "Bayview", 16),
        ("Alamo Square", "Chinatown", 15),
        ("Alamo Square", "Nob Hill", 11),
        ("Alamo Square", "Presidio", 17),
        ("Alamo Square", "Union Square", 14),
        ("Alamo Square", "The Castro", 8),
        ("Alamo Square", "North Beach", 15),
        ("Alamo Square", "Fisherman's Wharf", 19),
        ("Alamo Square", "Marina District", 15),
        ("Nob Hill", "Embarcadero", 9),
        ("Nob Hill", "Bayview", 19),
        ("Nob Hill", "Chinatown", 6),
        ("Nob Hill", "Alamo Square", 11),
        ("Nob Hill", "Presidio", 17),
        ("Nob Hill", "Union Square", 7),
        ("Nob Hill", "The Castro", 17),
        ("Nob Hill", "North Beach", 8),
        ("Nob Hill", "Fisherman's Wharf", 10),
        ("Nob Hill", "Marina District", 11),
        ("Presidio", "Embarcadero", 20),
        ("Presidio", "Bayview", 31),
        ("Presidio", "Chinatown", 21),
        ("Presidio", "Alamo Square", 19),
        ("Presidio", "Nob Hill", 18),
        ("Presidio", "Union Square", 22),
        ("Presidio", "The Castro", 21),
        ("Presidio", "North Beach", 18),
        ("Presidio", "Fisherman's Wharf", 19),
        ("Presidio", "Marina District", 11),
        ("Union Square", "Embarcadero", 11),
        ("Union Square", "Bayview", 15),
        ("Union Square", "Chinatown", 7),
        ("Union Square", "Alamo Square", 15),
        ("Union Square", "Nob Hill", 9),
        ("Union Square", "Presidio", 24),
        ("Union Square", "The Castro", 17),
        ("Union Square", "North Beach", 10),
        ("Union Square", "Fisherman's Wharf", 15),
        ("Union Square", "Marina District", 18),
        ("The Castro", "Embarcadero", 22),
        ("The Castro", "Bayview", 19),
        ("The Castro", "Chinatown", 22),
        ("The Castro", "Alamo Square", 8),
        ("The Castro", "Nob Hill", 16),
        ("The Castro", "Presidio", 20),
        ("The Castro", "Union Square", 19),
        ("The Castro", "North Beach", 20),
        ("The Castro", "Fisherman's Wharf", 24),
        ("The Castro", "Marina District", 21),
        ("North Beach", "Embarcadero", 6),
        ("North Beach", "Bayview", 25),
        ("North Beach", "Chinatown", 6),
        ("North Beach", "Alamo Square", 16),
        ("North Beach", "Nob Hill", 7),
        ("North Beach", "Presidio", 17),
        ("North Beach", "Union Square", 7),
        ("North Beach", "The Castro", 23),
        ("North Beach", "Fisherman's Wharf", 5),
        ("North Beach", "Marina District", 9),
        ("Fisherman's Wharf", "Embarcadero", 8),
        ("Fisherman's Wharf", "Bayview", 26),
        ("Fisherman's Wharf", "Chinatown", 12),
        ("Fisherman's Wharf", "Alamo Square", 21),
        ("Fisherman's Wharf", "Nob Hill", 11),
        ("Fisherman's Wharf", "Presidio", 17),
        ("Fisherman's Wharf", "Union Square", 13),
        ("Fisherman's Wharf", "The Castro", 27),
        ("Fisherman's Wharf", "North Beach", 6),
        ("Fisherman's Wharf", "Marina District", 9),
        ("Marina District", "Embarcadero", 14),
        ("Marina District", "Bayview", 27),
        ("Marina District", "Chinatown", 15),
        ("Marina District", "Alamo Square", 15),
        ("Marina District", "Nob Hill", 12),
        ("Marina District", "Presidio", 10),
        ("Marina District", "Union Square", 16),
        ("Marina District", "The Castro", 22),
        ("Marina District", "North Beach", 11),
        ("Marina District", "Fisherman's Wharf", 10)
    ]
    
    travel_time_dict = {}
    for item in travel_data:
        from_loc, to_loc, t = item
        travel_time_dict[(from_loc, to_loc)] = t

    # Friends data: (name, location, available_start (min from 9AM), available_end, min_duration)
    friends = [
        ("Matthew", "Bayview", 615, 780, 120),
        ("Karen", "Chinatown", 615, 735, 90),
        ("Sarah", "Alamo Square", 660, 765, 105),
        ("Jessica", "Nob Hill", 450, 585, 120),
        ("Stephanie", "Presidio", 0, 75, 60),  # available from 7:30AM to 10:15AM, but we start at 9:00AM (0 min) -> earliest arrival: 20 min, ends by 75 min -> max meeting 55 min < 60 -> impossible
        ("Mary", "Union Square", 465, 750, 60),
        ("Charles", "The Castro", 450, 780, 105),
        ("Nancy", "North Beach", 345, 660, 15),
        ("Thomas", "Fisherman's Wharf", 270, 600, 30),
        ("Brian", "Marina District", 195, 540, 60)
    ]
    
    n_friends = len(friends)
    n_events = n_friends + 1  # including the dummy event at the start
    
    s = Optimize()
    
    # active[0] is for dummy (always True). active[1..n_friends] for friends
    active = [True]  # dummy is always active
    active_vars = []
    for i in range(n_friends):
        active_var = Bool(f"active_{i}")
        active_vars.append(active_var)
        active.append(active_var)
    
    # Locations: event0 (dummy) is "Embarcadero", event i (i>=1) is friends[i-1][1]
    locations = ["Embarcadero"]  # for dummy
    for i in range(n_friends):
        locations.append(friends[i][1])
    
    # Start and end times: 
    #   start[0] = 0, end[0] = 0 (for dummy)
    #   for i in 1..n_friends: start[i] and end[i] are Int variables
    starts = [0]  # dummy
    ends = [0]    # dummy
    start_vars = []
    end_vars = []
    for i in range(n_friends):
        start_var = Int(f"start_{i}")
        end_var = Int(f"end_{i}")
        start_vars.append(start_var)
        end_vars.append(end_var)
        starts.append(start_var)
        ends.append(end_var)
    
    # Constraints for each friend: if active, then set end = start + min_duration, and within available time
    for i in range(1, n_events):
        friend_index = i-1
        min_dur = friends[friend_index][4]
        avail_start = friends[friend_index][2]
        avail_end = friends[friend_index][3]
        # If active, then set end = start + min_dur, and start >= avail_start, end <= avail_end
        s.add(Implies(active[i], ends[i] == starts[i] + min_dur))
        s.add(Implies(active[i], starts[i] >= avail_start))
        s.add(Implies(active[i], ends[i] <= avail_end))
    
    # Constraints for travel times between every pair of events (including dummy)
    for i in range(n_events):
        for j in range(i+1, n_events):
            # If both active, then disjunctive constraint
            loc_i = locations[i]
            loc_j = locations[j]
            travel_ij = travel_time_dict[(loc_i, loc_j)]
            travel_ji = travel_time_dict[(loc_j, loc_i)]
            if i == 0:  # dummy (index0) is always active
                # Only require constraint if j is active
                s.add(Implies(active[j], starts[j] >= ends[i] + travel_ij))
            else:
                # Both i and j are friends (or one dummy and one friend, but i>=1 so both are friends)
                constraint = Or(
                    starts[j] >= ends[i] + travel_ij,
                    starts[i] >= ends[j] + travel_ji
                )
                s.add(Implies(And(active[i], active[j]), constraint))
    
    # Maximize the number of active friends
    s.maximize(Sum([If(active_vars[i], 1, 0) for i in range(n_friends)]))
    
    # Check and get the solution
    if s.check() == sat:
        m = s.model()
        total_friends = 0
        schedule = []
        for i in range(n_friends):
            if m.evaluate(active_vars[i]):
                total_friends += 1
                start_val = m.evaluate(starts[i+1])
                end_val = m.evaluate(ends[i+1])
                # Convert minutes from 9AM to time string
                def minutes_to_time(minutes):
                    total_min = minutes.as_long()
                    hour = 9 + total_min // 60
                    minute = total_min % 60
                    am_pm = "AM" if hour < 12 else "PM"
                    if hour > 12:
                        hour -= 12
                    return f"{hour}:{minute:02d} {am_pm}"
                start_str = minutes_to_time(start_val)
                end_str = minutes_to_time(end_val)
                schedule.append((friends[i][0], friends[i][1], start_str, end_str))
        print(f"SOLUTION: We can meet {total_friends} friends.")
        print("Schedule:")
        for name, loc, start_t, end_t in schedule:
            print(f"  Meet {name} at {loc} from {start_t} to {end_t}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()