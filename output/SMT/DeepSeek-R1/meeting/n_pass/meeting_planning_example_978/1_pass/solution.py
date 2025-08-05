from z3 import *
import json

def main():
    # Define the friends with their details: name, location, (available_start, available_end) in minutes, and min_duration in minutes.
    friends = [
        ("Stephanie", "Fisherman's Wharf", (15*60+30, 22*60), 30),    # 15:30 to 22:00
        ("Lisa", "Financial District", (10*60+45, 17*60+15), 15),      # 10:45 to 17:15
        ("Melissa", "Russian Hill", (17*60, 21*60+45), 120),           # 17:00 to 21:45
        ("Betty", "Marina District", (10*60+45, 14*60+15), 60),        # 10:45 to 14:15
        ("Sarah", "Richmond District", (16*60+15, 19*60+30), 105),     # 16:15 to 19:30
        ("Daniel", "Pacific Heights", (18*60+30, 21*60+45), 60),       # 18:30 to 21:45
        ("Joshua", "Haight-Ashbury", (9*60, 15*60+30), 15),            # 09:00 to 15:30
        ("Joseph", "Presidio", (7*60, 13*60), 45),                     # 07:00 to 13:00 -> but we start at 9:00
        ("Andrew", "Nob Hill", (19*60+45, 22*60), 105),                # 19:45 to 22:00
        ("John", "The Castro", (13*60+15, 19*60+45), 45)               # 13:15 to 19:45
    ]
    
    # Build the travel time dictionary from the provided text
    travel_text = """Embarcadero to Fisherman's Wharf: 6
Embarcadero to Financial District: 5
Embarcadero to Russian Hill: 8
Embarcadero to Marina District: 12
Embarcadero to Richmond District: 21
Embarcadero to Pacific Heights: 11
Embarcadero to Haight-Ashbury: 21
Embarcadero to Presidio: 20
Embarcadero to Nob Hill: 10
Embarcadero to The Castro: 25
Fisherman's Wharf to Embarcadero: 8
Fisherman's Wharf to Financial District: 11
Fisherman's Wharf to Russian Hill: 7
Fisherman's Wharf to Marina District: 9
Fisherman's Wharf to Richmond District: 18
Fisherman's Wharf to Pacific Heights: 12
Fisherman's Wharf to Haight-Ashbury: 22
Fisherman's Wharf to Presidio: 17
Fisherman's Wharf to Nob Hill: 11
Fisherman's Wharf to The Castro: 27
Financial District to Embarcadero: 4
Financial District to Fisherman's Wharf: 10
Financial District to Russian Hill: 11
Financial District to Marina District: 15
Financial District to Richmond District: 21
Financial District to Pacific Heights: 13
Financial District to Haight-Ashbury: 19
Financial District to Presidio: 22
Financial District to Nob Hill: 8
Financial District to The Castro: 20
Russian Hill to Embarcadero: 8
Russian Hill to Fisherman's Wharf: 7
Russian Hill to Financial District: 11
Russian Hill to Marina District: 7
Russian Hill to Richmond District: 14
Russian Hill to Pacific Heights: 7
Russian Hill to Haight-Ashbury: 17
Russian Hill to Presidio: 14
Russian Hill to Nob Hill: 5
Russian Hill to The Castro: 21
Marina District to Embarcadero: 14
Marina District to Fisherman's Wharf: 10
Marina District to Financial District: 17
Marina District to Russian Hill: 8
Marina District to Richmond District: 11
Marina District to Pacific Heights: 7
Marina District to Haight-Ashbury: 16
Marina District to Presidio: 10
Marina District to Nob Hill: 12
Marina District to The Castro: 22
Richmond District to Embarcadero: 19
Richmond District to Fisherman's Wharf: 18
Richmond District to Financial District: 22
Richmond District to Russian Hill: 13
Richmond District to Marina District: 9
Richmond District to Pacific Heights: 10
Richmond District to Haight-Ashbury: 10
Richmond District to Presidio: 7
Richmond District to Nob Hill: 17
Richmond District to The Castro: 16
Pacific Heights to Embarcadero: 10
Pacific Heights to Fisherman's Wharf: 13
Pacific Heights to Financial District: 13
Pacific Heights to Russian Hill: 7
Pacific Heights to Marina District: 6
Pacific Heights to Richmond District: 12
Pacific Heights to Haight-Ashbury: 11
Pacific Heights to Presidio: 11
Pacific Heights to Nob Hill: 8
Pacific Heights to The Castro: 16
Haight-Ashbury to Embarcadero: 20
Haight-Ashbury to Fisherman's Wharf: 23
Haight-Ashbury to Financial District: 21
Haight-Ashbury to Russian Hill: 17
Haight-Ashbury to Marina District: 17
Haight-Ashbury to Richmond District: 10
Haight-Ashbury to Pacific Heights: 12
Haight-Ashbury to Presidio: 15
Haight-Ashbury to Nob Hill: 15
Haight-Ashbury to The Castro: 6
Presidio to Embarcadero: 20
Presidio to Fisherman's Wharf: 19
Presidio to Financial District: 23
Presidio to Russian Hill: 14
Presidio to Marina District: 11
Presidio to Richmond District: 7
Presidio to Pacific Heights: 11
Presidio to Haight-Ashbury: 15
Presidio to Nob Hill: 18
Presidio to The Castro: 21
Nob Hill to Embarcadero: 9
Nob Hill to Fisherman's Wharf: 10
Nob Hill to Financial District: 9
Nob Hill to Russian Hill: 5
Nob Hill to Marina District: 11
Nob Hill to Richmond District: 14
Nob Hill to Pacific Heights: 8
Nob Hill to Haight-Ashbury: 13
Nob Hill to Presidio: 17
Nob Hill to The Castro: 17
The Castro to Embarcadero: 22
The Castro to Fisherman's Wharf: 24
The Castro to Financial District: 21
The Castro to Russian Hill: 18
The Castro to Marina District: 21
The Castro to Richmond District: 16
The Castro to Pacific Heights: 16
The Castro to Haight-Ashbury: 6
The Castro to Presidio: 20
The Castro to Nob Hill: 16"""
    
    travel_dict = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        parts = line.split(':')
        if len(parts) < 2:
            continue
        from_to_str = parts[0].strip()
        time_str = parts[1].strip()
        if time_str.endswith('.'):
            time_str = time_str[:-1]
        time_val = int(time_str)
        from_to_parts = from_to_str.split(' to ')
        if len(from_to_parts) != 2:
            continue
        from_loc = from_to_parts[0].strip()
        to_loc = from_to_parts[1].strip()
        travel_dict[(from_loc, to_loc)] = time_val

    # We start at Embarcadero at 540 minutes (9:00 AM)
    n = len(friends)
    s = Optimize()
    s.set("timeout", 300000)  # 5 minutes timeout

    # Create variables for each friend
    meet_vars = []
    start_vars = []
    end_vars = []
    order_vars = []
    for i, (name, loc, (avail_start, avail_end), min_dur) in enumerate(friends):
        meet_vars.append(Bool(f"meet_{i}"))
        start_vars.append(Int(f"start_{i}"))
        end_vars.append(Int(f"end_{i}"))
        order_vars.append(Int(f"order_{i}"))

    # Constraints for each friend
    for i, (name, loc, (avail_start, avail_end), min_dur) in enumerate(friends):
        # If we meet this friend, then:
        s.add(If(meet_vars[i],
                 And(
                     start_vars[i] >= max(avail_start, 540 + travel_dict[("Embarcadero", loc)]),
                     end_vars[i] <= avail_end,
                     end_vars[i] == start_vars[i] + min_dur,   # We set the meeting to exactly the minimum duration to maximize the chance of meeting more friends.
                     order_vars[i] >= 0,
                     order_vars[i] < n
                 ),
                 True))   # if not meeting, no constraints

    # Constraints for every pair of distinct friends
    for i in range(n):
        for j in range(i+1, n):
            # If both i and j are met, then:
            c1 = Implies(And(meet_vars[i], meet_vars[j]), order_vars[i] != order_vars[j])
            # Ordering constraints with travel times
            # If i before j: then start_j >= end_i + travel(i_loc, j_loc)
            loc_i = friends[i][1]
            loc_j = friends[j][1]
            travel_ij = travel_dict.get((loc_i, loc_j))
            travel_ji = travel_dict.get((loc_j, loc_i))
            if travel_ij is None or travel_ji is None:
                # Should not happen, but skip if missing
                continue
            c2 = Implies(And(meet_vars[i], meet_vars[j], order_vars[i] < order_vars[j]),
                         start_vars[j] >= end_vars[i] + travel_ij)
            c3 = Implies(And(meet_vars[i], meet_vars[j], order_vars[j] < order_vars[i]),
                         start_vars[i] >= end_vars[j] + travel_ji)
            s.add(c1)
            s.add(c2)
            s.add(c3)

    # Objective: maximize the number of friends met
    s.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(n)]))

    # Solve
    result = s.check()
    itinerary_list = []
    if result == sat:
        m = s.model()
        scheduled_meetings = []
        for i, (name, loc, (avail_start, avail_end), min_dur) in enumerate(friends):
            if is_true(m[meet_vars[i]]):
                start_val = m.evaluate(start_vars[i]).as_long()
                end_val = m.evaluate(end_vars[i]).as_long()
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                scheduled_meetings.append( (start_val, {"action": "meet", "person": name, "start_time": start_str, "end_time": end_str}) )
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary_list = [m[1] for m in scheduled_meetings]
    else:
        # If no solution found, return empty itinerary
        itinerary_list = []

    # Output the itinerary in JSON format
    result_dict = {"itinerary": itinerary_list}
    print("SOLUTION:")
    print(json.dumps(result_dict))

if __name__ == "__main__":
    main()