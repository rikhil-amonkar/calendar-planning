from z3 import *
import json

def main():
    # Friends data: (name, location, available_start (min), available_end (min), min_duration (min))
    friends = [
        ("Betty", "Russian Hill", 420, 1005, 105),
        ("Melissa", "Alamo Square", 570, 1035, 105),
        ("Joshua", "Haight-Ashbury", 735, 1140, 90),
        ("Jeffrey", "Marina District", 735, 1080, 45),
        ("James", "Bayview", 450, 1200, 90),
        ("Anthony", "Chinatown", 705, 810, 75),
        ("Timothy", "Presidio", 750, 885, 90),
        ("Emily", "Sunset District", 1170, 1290, 120)
    ]
    
    # Build travel_dict from provided travel data
    travel_data_text = """
Union Square to Russian Hill: 13
Union Square to Alamo Square: 15
Union Square to Haight-Ashbury: 18
Union Square to Marina District: 18
Union Square to Bayview: 15
Union Square to Chinatown: 7
Union Square to Presidio: 24
Union Square to Sunset District: 27
Russian Hill to Union Square: 10
Russian Hill to Alamo Square: 15
Russian Hill to Haight-Ashbury: 17
Russian Hill to Marina District: 7
Russian Hill to Bayview: 23
Russian Hill to Chinatown: 9
Russian Hill to Presidio: 14
Russian Hill to Sunset District: 23
Alamo Square to Union Square: 14
Alamo Square to Russian Hill: 13
Alamo Square to Haight-Ashbury: 5
Alamo Square to Marina District: 15
Alamo Square to Bayview: 16
Alamo Square to Chinatown: 15
Alamo Square to Presidio: 17
Alamo Square to Sunset District: 16
Haight-Ashbury to Union Square: 19
Haight-Ashbury to Russian Hill: 17
Haight-Ashbury to Alamo Square: 5
Haight-Ashbury to Marina District: 17
Haight-Ashbury to Bayview: 18
Haight-Ashbury to Chinatown: 19
Haight-Ashbury to Presidio: 15
Haight-Ashbury to Sunset District: 15
Marina District to Union Square: 16
Marina District to Russian Hill: 8
Marina District to Alamo Square: 15
Marina District to Haight-Ashbury: 16
Marina District to Bayview: 27
Marina District to Chinatown: 15
Marina District to Presidio: 10
Marina District to Sunset District: 19
Bayview to Union Square: 18
Bayview to Russian Hill: 23
Bayview to Alamo Square: 16
Bayview to Haight-Ashbury: 19
Bayview to Marina District: 27
Bayview to Chinatown: 19
Bayview to Presidio: 32
Bayview to Sunset District: 23
Chinatown to Union Square: 7
Chinatown to Russian Hill: 7
Chinatown to Alamo Square: 17
Chinatown to Haight-Ashbury: 19
Chinatown to Marina District: 12
Chinatown to Bayview: 20
Chinatown to Presidio: 19
Chinatown to Sunset District: 29
Presidio to Union Square: 22
Presidio to Russian Hill: 14
Presidio to Alamo Square: 19
Presidio to Haight-Ashbury: 15
Presidio to Marina District: 11
Presidio to Bayview: 31
Presidio to Chinatown: 21
Presidio to Sunset District: 15
Sunset District to Union Square: 30
Sunset District to Russian Hill: 24
Sunset District to Alamo Square: 17
Sunset District to Haight-Ashbury: 15
Sunset District to Marina District: 21
Sunset District to Bayview: 22
Sunset District to Chinatown: 30
Sunset District to Presidio: 16
    """
    travel_dict = {}
    entries = travel_data_text.strip().split('\n')
    for entry in entries:
        if not entry.strip():
            continue
        parts = entry.split(':')
        if len(parts) < 2:
            continue
        locations_part = parts[0].strip()
        time_val = int(parts[1].strip())
        if ' to ' in locations_part:
            from_loc, to_loc = locations_part.split(' to ')
            from_loc = from_loc.strip()
            to_loc = to_loc.strip()
            travel_dict[(from_loc, to_loc)] = time_val

    # Initialize Z3 solver with optimization
    s = Optimize()
    
    # Decision variables
    active = [Bool(f'active_{i}') for i in range(8)]
    start_times = [Int(f'start_{i}') for i in range(8)]
    
    # Constraints for each friend
    for i in range(8):
        name, loc, avail_start, avail_end, dur = friends[i]
        # If active, meeting must be within availability window
        s.add(Implies(active[i], start_times[i] >= avail_start))
        s.add(Implies(active[i], start_times[i] + dur <= avail_end))
    
    # Emily must start at 19:30 if active
    s.add(Implies(active[7], start_times[7] == 1170))
    
    # Constraints for travel from Union Square or from another meeting
    for i in range(8):
        name_i, loc_i, _, _, dur_i = friends[i]
        from_union = travel_dict[('Union Square', loc_i)]
        # Condition: start_times[i] >= 540 + from_union OR exists j (active[j] and start_times[i] >= start_times[j] + friends[j][4] + travel_dict[(friends[j][1], loc_i)])
        options = [start_times[i] >= 540 + from_union]
        for j in range(8):
            if i == j:
                continue
            name_j, loc_j, _, _, dur_j = friends[j]
            travel_time_ij = travel_dict.get((loc_j, loc_i), None)
            if travel_time_ij is None:
                # Should not happen as we have all pairs
                continue
            cond_j = And(active[j], start_times[i] >= start_times[j] + dur_j + travel_time_ij)
            options.append(cond_j)
        s.add(Implies(active[i], Or(options)))
    
    # Constraints for non-overlapping meetings with travel times
    for i in range(8):
        for j in range(i+1, 8):
            loc_i = friends[i][1]
            loc_j = friends[j][1]
            dur_i = friends[i][4]
            dur_j = friends[j][4]
            travel_ij = travel_dict.get((loc_i, loc_j), None)
            travel_ji = travel_dict.get((loc_j, loc_i), None)
            if travel_ij is None or travel_ji is None:
                continue
            constraint = Or(
                start_times[i] >= start_times[j] + dur_j + travel_ji,
                start_times[j] >= start_times[i] + dur_i + travel_ij
            )
            s.add(Implies(And(active[i], active[j]), constraint))
    
    # Objective: maximize the number of active meetings
    total_active = Sum([If(active[i], 1, 0) for i in range(8)])
    s.maximize(total_active)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(8):
            if is_true(m.evaluate(active[i])):
                start_val = m.evaluate(start_times[i]).as_long()
                dur = friends[i][4]
                end_val = start_val + dur
                # Format to HH:MM
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_time_str = f"{start_hour:02d}:{start_minute:02d}"
                end_time_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i][0],
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()