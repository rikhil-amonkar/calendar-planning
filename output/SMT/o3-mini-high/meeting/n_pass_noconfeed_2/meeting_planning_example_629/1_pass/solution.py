import json
from z3 import *

def format_time(t):
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times (in minutes)
    travel_times = {
        "Russian Hill": {
            "Presidio": 14,
            "Chinatown": 9,
            "Pacific Heights": 7,
            "Richmond District": 14,
            "Fisherman's Wharf": 7,
            "Golden Gate Park": 21,
            "Bayview": 23
        },
        "Presidio": {
            "Russian Hill": 14,
            "Chinatown": 21,
            "Pacific Heights": 11,
            "Richmond District": 7,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 12,
            "Bayview": 31
        },
        "Chinatown": {
            "Russian Hill": 7,
            "Presidio": 19,
            "Pacific Heights": 10,
            "Richmond District": 20,
            "Fisherman's Wharf": 8,
            "Golden Gate Park": 23,
            "Bayview": 22
        },
        "Pacific Heights": {
            "Russian Hill": 7,
            "Presidio": 11,
            "Chinatown": 11,
            "Richmond District": 12,
            "Fisherman's Wharf": 13,
            "Golden Gate Park": 15,
            "Bayview": 22
        },
        "Richmond District": {
            "Russian Hill": 13,
            "Presidio": 7,
            "Chinatown": 20,
            "Pacific Heights": 10,
            "Fisherman's Wharf": 18,
            "Golden Gate Park": 9,
            "Bayview": 26
        },
        "Fisherman's Wharf": {
            "Russian Hill": 7,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12,
            "Richmond District": 18,
            "Golden Gate Park": 25,
            "Bayview": 26
        },
        "Golden Gate Park": {
            "Russian Hill": 19,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16,
            "Richmond District": 7,
            "Fisherman's Wharf": 24,
            "Bayview": 23
        },
        "Bayview": {
            "Russian Hill": 23,
            "Presidio": 31,
            "Chinatown": 18,
            "Pacific Heights": 23,
            "Richmond District": 25,
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22
        }
    }

    # Friends with meeting constraints (times in minutes since midnight)
    friends = [
        {"name": "Matthew", "location": "Presidio", "avail_start": 660, "avail_end": 1260, "min_duration": 90},
        {"name": "Margaret", "location": "Chinatown", "avail_start": 555, "avail_end": 1125, "min_duration": 90},
        {"name": "Nancy", "location": "Pacific Heights", "avail_start": 855, "avail_end": 1020, "min_duration": 15},
        {"name": "Helen", "location": "Richmond District", "avail_start": 1185, "avail_end": 1320, "min_duration": 60},
        {"name": "Rebecca", "location": "Fisherman's Wharf", "avail_start": 1275, "avail_end": 1335, "min_duration": 60},
        {"name": "Kimberly", "location": "Golden Gate Park", "avail_start": 780, "avail_end": 990, "min_duration": 120},
        {"name": "Kenneth", "location": "Bayview", "avail_start": 870, "avail_end": 1080, "min_duration": 60}
    ]

    num_meetings = len(friends)
    # Create an optimizer
    opt = Optimize()

    # Decision variables for each friend meeting
    scheduled = [Bool(f"scheduled_{i}") for i in range(num_meetings)]
    start = [Int(f"start_{i}") for i in range(num_meetings)]
    end = [Int(f"end_{i}") for i in range(num_meetings)]
    order = [Int(f"order_{i}") for i in range(num_meetings)]
    
    # Constraints for each meeting if scheduled, and dummy values if not.
    for i, friend in enumerate(friends):
        # If meeting is scheduled, enforce availability and duration
        opt.add(Implies(scheduled[i], start[i] >= friend["avail_start"]))
        opt.add(Implies(scheduled[i], end[i] <= friend["avail_end"]))
        opt.add(Implies(scheduled[i], end[i] - start[i] >= friend["min_duration"]))
        # If scheduled, order must be between 1 and num_meetings; if not, order is 0.
        opt.add(Implies(scheduled[i], And(order[i] >= 1, order[i] <= num_meetings)))
        opt.add(Implies(Not(scheduled[i]), order[i] == 0))
        # Set dummy times if not scheduled.
        opt.add(Implies(Not(scheduled[i]), start[i] == 0))
        opt.add(Implies(Not(scheduled[i]), end[i] == 0))
        # Domain for times
        opt.add(start[i] >= 0, start[i] <= 1440)
        opt.add(end[i] >= 0, end[i] <= 1440)

    # Ensure that scheduled meetings have distinct order values.
    for i in range(num_meetings):
        for j in range(i+1, num_meetings):
            opt.add(Implies(And(scheduled[i], scheduled[j]), order[i] != order[j]))

    # Enforce consecutiveness: if a meeting has order > 1, there must be another meeting with order one less.
    for i in range(num_meetings):
        opt.add(Implies(
            And(scheduled[i], order[i] > 1),
            Or([And(scheduled[j], order[j] == order[i] - 1) for j in range(num_meetings) if j != i])
        ))

    # Travel time constraints between consecutive meetings:
    for i in range(num_meetings):
        for j in range(num_meetings):
            if i != j:
                # If meeting j is immediately after meeting i in the schedule, account for travel time.
                opt.add(Implies(
                    And(scheduled[i], scheduled[j], order[j] == order[i] + 1),
                    start[j] >= end[i] + travel_times[friends[i]["location"]][friends[j]["location"]]
                ))

    # For the first scheduled meeting, include travel from the starting point "Russian Hill" at 9:00 (540 minutes)
    for i in range(num_meetings):
        opt.add(Implies(
            And(scheduled[i], order[i] == 1),
            start[i] >= 540 + travel_times["Russian Hill"][friends[i]["location"]]
        ))

    # Objective: Maximize the number of meetings scheduled
    total_meetings = Sum([If(s, 1, 0) for s in scheduled])
    opt.maximize(total_meetings)
    
    # Check for a solution and build itinerary
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # Collect scheduled meetings (order, location, person, start, end)
        scheduled_meetings = []
        for i, friend in enumerate(friends):
            if is_true(model.evaluate(scheduled[i])):
                ord_val = model.evaluate(order[i]).as_long()
                start_val = model.evaluate(start[i]).as_long()
                end_val = model.evaluate(end[i]).as_long()
                scheduled_meetings.append((ord_val, friend["location"], friend["name"], start_val, end_val))
        # Sort meetings by their order in the schedule
        scheduled_meetings.sort(key=lambda x: x[0])
        for ord_val, location, person, start_val, end_val in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(start_val),
                "end_time": format_time(end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == '__main__':
    main()