from z3 import *
import json

def min_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define friend meeting parameters:
    # Times are in minutes from midnight.
    # 9:00 AM is 540 minutes.
    friends = [
        {"name": "David", "location": "Mission District", "avail_start": 480, "avail_end": 1185, "min_duration": 45},
        {"name": "Kenneth", "location": "Alamo Square", "avail_start": 840, "avail_end": 1185, "min_duration": 120},
        {"name": "John", "location": "Pacific Heights", "avail_start": 1020, "avail_end": 1200, "min_duration": 15},
        {"name": "Charles", "location": "Union Square", "avail_start": 1305, "avail_end": 1365, "min_duration": 60},
        {"name": "Deborah", "location": "Golden Gate Park", "avail_start": 420, "avail_end": 1095, "min_duration": 90},
        {"name": "Karen", "location": "Sunset District", "avail_start": 1065, "avail_end": 1275, "min_duration": 15},
        {"name": "Carol", "location": "Presidio", "avail_start": 495, "avail_end": 555, "min_duration": 30},
    ]
    
    # Travel times (in minutes) for directed edges between locations.
    travel_times = {
        ("Chinatown", "Mission District"): 18,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Presidio"): 19,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Presidio"): 25,
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Presidio"): 18,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Presidio"): 11,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Presidio"): 24,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Presidio"): 11,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Presidio"): 16,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Sunset District"): 15,
    }
    
    # Starting location is Chinatown at 9:00 AM (540 minutes)
    start_location = "Chinatown"
    start_time_offset = 540

    opt = Optimize()
    
    n = len(friends)
    # Decision variables: selected indicates if we meet friend i.
    selected = [Bool(f"sel_{i}") for i in range(n)]
    # start_vars and end_vars represent the meeting start and end times (in minutes) for friend i.
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    
    # Add constraints for each meeting if it is selected.
    for i, friend in enumerate(friends):
        # Meeting must occur within the friend's availability window.
        opt.add(Implies(selected[i], start_vars[i] >= friend["avail_start"]))
        opt.add(Implies(selected[i], end_vars[i] <= friend["avail_end"]))
        # Minimum meeting duration constraint.
        opt.add(Implies(selected[i], end_vars[i] - start_vars[i] >= friend["min_duration"]))
        # You must have arrived after traveling from the start location.
        travel_from_start = travel_times[(start_location, friend["location"])]
        opt.add(Implies(selected[i], start_vars[i] >= start_time_offset + travel_from_start))
        # Implicit: meeting start is before meeting end.
        opt.add(Implies(selected[i], start_vars[i] < end_vars[i]))
    
    # For every pair of meetings that are both selected, enforce non-overlap accounting for travel.
    for i in range(n):
        for j in range(i+1, n):
            travel_ij = travel_times[(friends[i]["location"], friends[j]["location"])]
            travel_ji = travel_times[(friends[j]["location"], friends[i]["location"])]
            # Either meeting i happens before j (with travel time) or vice versa.
            ordering = Or(
                end_vars[i] + travel_ij <= start_vars[j],
                end_vars[j] + travel_ji <= start_vars[i]
            )
            opt.add(Implies(And(selected[i], selected[j]), ordering))
    
    # Objective: maximize the number of meetings (i.e., friends met).
    total_meetings = Sum([If(selected[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        # Collect scheduled meetings from model.
        for i, friend in enumerate(friends):
            if is_true(model.evaluate(selected[i])):
                s_val = model.evaluate(start_vars[i]).as_long()
                e_val = model.evaluate(end_vars[i]).as_long()
                scheduled.append((s_val, {
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": min_to_time(s_val),
                    "end_time": min_to_time(e_val)
                }))
        # Sort meetings in order of start time.
        scheduled.sort(key=lambda x: x[0])
        itinerary = [meeting for _, meeting in scheduled]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()