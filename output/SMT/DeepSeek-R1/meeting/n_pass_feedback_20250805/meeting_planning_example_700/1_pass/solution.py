import json
from z3 import *

def main():
    # Travel time dictionary between locations (in minutes)
    travel_time = {
        "Presidio": {
            "North Beach": 18,
            "Fisherman's Wharf": 19,
            "Marina District": 11,
            "Alamo Square": 19,
            "Sunset District": 15,
            "Nob Hill": 18,
            "Golden Gate Park": 12
        },
        "North Beach": {
            "Presidio": 17,
            "Fisherman's Wharf": 5,
            "Marina District": 9,
            "Alamo Square": 16,
            "Sunset District": 27,
            "Nob Hill": 7,
            "Golden Gate Park": 22
        },
        "Fisherman's Wharf": {
            "Presidio": 17,
            "North Beach": 6,
            "Marina District": 9,
            "Alamo Square": 21,
            "Sunset District": 27,
            "Nob Hill": 11,
            "Golden Gate Park": 24
        },
        "Marina District": {
            "Presidio": 10,
            "North Beach": 11,
            "Fisherman's Wharf": 10,
            "Alamo Square": 15,
            "Sunset District": 19,
            "Nob Hill": 12,
            "Golden Gate Park": 18
        },
        "Alamo Square": {
            "Presidio": 17,
            "North Beach": 15,
            "Fisherman's Wharf": 19,
            "Marina District": 15,
            "Sunset District": 16,
            "Nob Hill": 11,
            "Golden Gate Park": 9
        },
        "Sunset District": {
            "Presidio": 16,
            "North Beach": 28,
            "Fisherman's Wharf": 29,
            "Marina District": 21,
            "Alamo Square": 17,
            "Nob Hill": 27,
            "Golden Gate Park": 11
        },
        "Nob Hill": {
            "Presidio": 17,
            "North Beach": 8,
            "Fisherman's Wharf": 10,
            "Marina District": 11,
            "Alamo Square": 11,
            "Sunset District": 24,
            "Golden Gate Park": 17
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "North Beach": 23,
            "Fisherman's Wharf": 24,
            "Marina District": 16,
            "Alamo Square": 9,
            "Sunset District": 10,
            "Nob Hill": 20
        }
    }

    # Define friends: (name, location, available_start (min), available_end (min), min_duration (min))
    friends = [
        ("Helen", "North Beach", 11*60, 12*60+15, 45),
        ("Emily", "Fisherman's Wharf", 16*60+15, 19*60, 30),
        ("Mark", "Marina District", 18*60+15, 19*60+45, 75),
        ("Barbara", "Alamo Square", 17*60, 19*60, 120),
        ("Laura", "Sunset District", 19*60, 21*60+15, 75),
        ("Mary", "Nob Hill", 17*60+30, 19*60, 45),
        ("Michelle", "Golden Gate Park", 20*60, 21*60, 15)
    ]
    n = len(friends)
    start_presidio = 9*60  # 9:00 AM in minutes

    # Create Z3 variables
    met = [Bool(f'met_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]

    s = Solver()

    # Constraints for each friend
    for i in range(n):
        name, loc, avail_start, avail_end, min_dur = friends[i]
        s.add(Implies(met[i], start[i] >= avail_start))
        s.add(Implies(met[i], end[i] <= avail_end))
        s.add(Implies(met[i], end[i] == start[i] + min_dur))
        # Travel from Presidio to friend's location
        s.add(Implies(met[i], start[i] >= start_presidio + travel_time["Presidio"][loc]))

    # Constraints for every pair of friends (i, j)
    for i in range(n):
        for j in range(i+1, n):
            loc_i = friends[i][1]
            loc_j = friends[j][1]
            t_ij = travel_time[loc_i][loc_j]
            t_ji = travel_time[loc_j][loc_i]
            # If both friends are met, ensure non-overlapping with travel time
            s.add(Implies(And(met[i], met[j]),
                            Or(end[i] + t_ij <= start[j], end[j] + t_ji <= start[i])))

    # Maximize the number of friends met
    opt = Optimize()
    opt.add(s.assertions())
    num_met = Sum([If(met_i, 1, 0) for met_i in met])
    opt.maximize(num_met)

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(n):
            if is_true(m.eval(met[i])):
                name = friends[i][0]
                start_min = m.eval(start[i]).as_long()
                end_min = m.eval(end[i]).as_long()
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by start_time
        itinerary.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()