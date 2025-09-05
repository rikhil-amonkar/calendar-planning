from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

def main():
    # Travel times in minutes between locations.
    travel = {
        "Chinatown": {
            "Embarcadero": 5,
            "Pacific Heights": 10,
            "Russian Hill": 7,
            "Haight-Ashbury": 19,
            "Golden Gate Park": 23,
            "Fisherman's Wharf": 8,
            "Sunset District": 29,
            "The Castro": 22
        },
        "Embarcadero": {
            "Chinatown": 7,
            "Pacific Heights": 11,
            "Russian Hill": 8,
            "Haight-Ashbury": 21,
            "Golden Gate Park": 25,
            "Fisherman's Wharf": 6,
            "Sunset District": 30,
            "The Castro": 25
        },
        "Pacific Heights": {
            "Chinatown": 11,
            "Embarcadero": 10,
            "Russian Hill": 7,
            "Haight-Ashbury": 11,
            "Golden Gate Park": 15,
            "Fisherman's Wharf": 13,
            "Sunset District": 21,
            "The Castro": 16
        },
        "Russian Hill": {
            "Chinatown": 9,
            "Embarcadero": 8,
            "Pacific Heights": 7,
            "Haight-Ashbury": 17,
            "Golden Gate Park": 21,
            "Fisherman's Wharf": 7,
            "Sunset District": 23,
            "The Castro": 21
        },
        "Haight-Ashbury": {
            "Chinatown": 19,
            "Embarcadero": 20,
            "Pacific Heights": 12,
            "Russian Hill": 17,
            "Golden Gate Park": 7,
            "Fisherman's Wharf": 23,
            "Sunset District": 15,
            "The Castro": 6
        },
        "Golden Gate Park": {
            "Chinatown": 23,
            "Embarcadero": 25,
            "Pacific Heights": 16,
            "Russian Hill": 19,
            "Haight-Ashbury": 7,
            "Fisherman's Wharf": 24,
            "Sunset District": 10,
            "The Castro": 13
        },
        "Fisherman's Wharf": {
            "Chinatown": 12,
            "Embarcadero": 8,
            "Pacific Heights": 12,
            "Russian Hill": 7,
            "Haight-Ashbury": 22,
            "Golden Gate Park": 25,
            "Sunset District": 27,
            "The Castro": 27
        },
        "Sunset District": {
            "Chinatown": 30,
            "Embarcadero": 30,
            "Pacific Heights": 21,
            "Russian Hill": 24,
            "Haight-Ashbury": 15,
            "Golden Gate Park": 11,
            "Fisherman's Wharf": 29,
            "The Castro": 17
        },
        "The Castro": {
            "Chinatown": 22,
            "Embarcadero": 22,
            "Pacific Heights": 16,
            "Russian Hill": 18,
            "Haight-Ashbury": 6,
            "Golden Gate Park": 11,
            "Fisherman's Wharf": 24,
            "Sunset District": 17
        }
    }

    # Friends' meeting constraints: Each friend is available at a specific location within a time window
    # and requires a minimum meeting duration.
    # Times are in minutes from midnight.
    friends = [
        {"name": "Richard", "location": "Embarcadero", "avail_start": 15*60 + 15, "avail_end": 18*60 + 45, "min_duration": 90},
        {"name": "Mark", "location": "Pacific Heights", "avail_start": 15*60, "avail_end": 17*60, "min_duration": 45},
        {"name": "Matthew", "location": "Russian Hill", "avail_start": 17*60 + 30, "avail_end": 21*60, "min_duration": 90},
        {"name": "Rebecca", "location": "Haight-Ashbury", "avail_start": 14*60 + 45, "avail_end": 18*60, "min_duration": 60},
        {"name": "Melissa", "location": "Golden Gate Park", "avail_start": 13*60 + 45, "avail_end": 17*60 + 30, "min_duration": 90},
        {"name": "Margaret", "location": "Fisherman's Wharf", "avail_start": 14*60 + 45, "avail_end": 20*60 + 15, "min_duration": 15},
        {"name": "Emily", "location": "Sunset District", "avail_start": 15*60 + 45, "avail_end": 17*60, "min_duration": 45},
        {"name": "George", "location": "The Castro", "avail_start": 14*60, "avail_end": 16*60 + 15, "min_duration": 75}
    ]

    n = len(friends)
    # Create an Optimize() solver instance
    opt = Optimize()

    # For each friend we decide if we attend (Bool), meeting start time (s), end time (e), and order of visit.
    attends = [Bool(f"attend_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]

    # Add constraints for each friend meeting.
    for i in range(n):
        friend = friends[i]
        # When we attend, meeting must lie within the friend's availability and have the required duration.
        opt.add(Implies(attends[i], s_vars[i] >= friend["avail_start"]))
        opt.add(Implies(attends[i], e_vars[i] <= friend["avail_end"]))
        opt.add(Implies(attends[i], e_vars[i] - s_vars[i] >= friend["min_duration"]))
        # If not attending, fix times to 0 (to avoid interference in ordering/travel constraints)
        opt.add(Implies(Not(attends[i]), And(s_vars[i] == 0, e_vars[i] == 0)))
        # If attended, assign an order between 1 and n; if not, order is 0.
        opt.add(Implies(attends[i], And(order_vars[i] >= 1, order_vars[i] <= n)))
        opt.add(Implies(Not(attends[i]), order_vars[i] == 0))

    # Ensure that attended meetings get a unique order.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(attends[i], attends[j]), order_vars[i] != order_vars[j]))

    # Add travel constraints between meetings:
    # For any two meetings i and j that are both attended,
    # if meeting i is scheduled before meeting j then j's start time must be at least
    # the end time of i plus travel time from i's location to j's location.
    for i in range(n):
        for j in range(n):
            if i != j:
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                travel_time = travel[loc_i][loc_j]
                opt.add(Implies(And(attends[i], attends[j], order_vars[i] < order_vars[j]),
                                s_vars[j] >= e_vars[i] + travel_time))
    
    # The first attended meeting must be reachable from initial arrival.
    # You arrive at Chinatown at 9:00 (540 minutes); add travel time from Chinatown.
    for i in range(n):
        loc_i = friends[i]["location"]
        travel_from_start = travel["Chinatown"][loc_i]
        opt.add(Implies(And(attends[i], order_vars[i] == 1),
                        s_vars[i] >= 540 + travel_from_start))

    # Objective: Maximize the number of meetings attended.
    total_meetings = Sum([If(attends[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    # Check for a solution.
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        scheduled = []
        for i in range(n):
            if m.evaluate(attends[i]):
                order_val = m.evaluate(order_vars[i]).as_long()
                s_val = m.evaluate(s_vars[i]).as_long()
                e_val = m.evaluate(e_vars[i]).as_long()
                scheduled.append((order_val, friends[i]["name"], friends[i]["location"], s_val, e_val))
        scheduled.sort(key=lambda x: x[0])
        for order_val, name, location, start, end in scheduled:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()