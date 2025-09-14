from z3 import *
import json

def minutes_to_time(m):
    # m is minutes from midnight
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Define meeting info: each friend with fixed location, availability window (in minutes from midnight) and minimum meeting duration.
    # Times are in minutes from midnight.
    meetings = [
        {"person": "Joshua", "location": "Embarcadero", "avail_start": 585, "avail_end": 1080, "min_duration": 105},       # 9:45 - 18:00
        {"person": "Jeffrey", "location": "Bayview", "avail_start": 585, "avail_end": 1215, "min_duration": 75},            # 9:45 - 20:15
        {"person": "Charles", "location": "Union Square", "avail_start": 645, "avail_end": 1215, "min_duration": 120},       # 10:45 - 20:15
        {"person": "Joseph", "location": "Chinatown", "avail_start": 420, "avail_end": 930, "min_duration": 60},             # 7:00 - 15:30
        {"person": "Elizabeth", "location": "Sunset District", "avail_start": 540, "avail_end": 585, "min_duration": 45},    # 9:00 - 9:45
        {"person": "Matthew", "location": "Golden Gate Park", "avail_start": 660, "avail_end": 1170, "min_duration": 45},    # 11:00 - 19:30
        {"person": "Carol", "location": "Financial District", "avail_start": 645, "avail_end": 675, "min_duration": 15},     # 10:45 - 11:15
        {"person": "Paul", "location": "Haight-Ashbury", "avail_start": 1155, "avail_end": 1230, "min_duration": 15},         # 19:15 - 20:30
        {"person": "Rebecca", "location": "Mission District", "avail_start": 1020, "avail_end": 1305, "min_duration": 45}     # 17:00 - 21:45
    ]

    # Travel times (in minutes) between locations.
    travel = {
        "Marina District": {
            "Embarcadero": 14,
            "Bayview": 27,
            "Union Square": 16,
            "Chinatown": 15,
            "Sunset District": 19,
            "Golden Gate Park": 18,
            "Financial District": 17,
            "Haight-Ashbury": 16,
            "Mission District": 20
        },
        "Embarcadero": {
            "Marina District": 12,
            "Bayview": 21,
            "Union Square": 10,
            "Chinatown": 7,
            "Sunset District": 30,
            "Golden Gate Park": 25,
            "Financial District": 5,
            "Haight-Ashbury": 21,
            "Mission District": 20
        },
        "Bayview": {
            "Marina District": 27,
            "Embarcadero": 19,
            "Union Square": 18,
            "Chinatown": 19,
            "Sunset District": 23,
            "Golden Gate Park": 22,
            "Financial District": 19,
            "Haight-Ashbury": 19,
            "Mission District": 13
        },
        "Union Square": {
            "Marina District": 18,
            "Embarcadero": 11,
            "Bayview": 15,
            "Chinatown": 7,
            "Sunset District": 27,
            "Golden Gate Park": 22,
            "Financial District": 9,
            "Haight-Ashbury": 18,
            "Mission District": 14
        },
        "Chinatown": {
            "Marina District": 12,
            "Embarcadero": 5,
            "Bayview": 20,
            "Union Square": 7,
            "Sunset District": 29,
            "Golden Gate Park": 23,
            "Financial District": 5,
            "Haight-Ashbury": 19,
            "Mission District": 17
        },
        "Sunset District": {
            "Marina District": 21,
            "Embarcadero": 30,
            "Bayview": 22,
            "Union Square": 30,
            "Chinatown": 30,
            "Golden Gate Park": 11,
            "Financial District": 30,
            "Haight-Ashbury": 15,
            "Mission District": 25
        },
        "Golden Gate Park": {
            "Marina District": 16,
            "Embarcadero": 25,
            "Bayview": 23,
            "Union Square": 22,
            "Chinatown": 23,
            "Sunset District": 10,
            "Financial District": 26,
            "Haight-Ashbury": 7,
            "Mission District": 17
        },
        "Financial District": {
            "Marina District": 15,
            "Embarcadero": 4,
            "Bayview": 19,
            "Union Square": 9,
            "Chinatown": 5,
            "Sunset District": 30,
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Mission District": 17
        },
        "Haight-Ashbury": {
            "Marina District": 17,
            "Embarcadero": 20,
            "Bayview": 18,
            "Union Square": 19,
            "Chinatown": 19,
            "Sunset District": 15,
            "Golden Gate Park": 7,
            "Financial District": 21,
            "Mission District": 11
        },
        "Mission District": {
            "Marina District": 19,
            "Embarcadero": 19,
            "Bayview": 14,
            "Union Square": 15,
            "Chinatown": 16,
            "Sunset District": 24,
            "Golden Gate Park": 17,
            "Financial District": 15,
            "Haight-Ashbury": 12
        }
    }

    # Create the Optimize solver.
    opt = Optimize()

    n = len(meetings)
    # For each meeting, create decision variables:
    # scheduled[i] is a Boolean indicating whether meeting i is scheduled.
    # order_vars[i] is an integer representing the ordering (0 if not scheduled, >=1 if scheduled).
    # start_vars[i] and end_vars[i] represent the meeting start and end times in minutes.
    scheduled = [ Bool(f"scheduled_{i}") for i in range(n) ]
    order_vars = [ Int(f"order_{i}") for i in range(n) ]
    start_vars = [ Int(f"start_{i}") for i in range(n) ]
    end_vars = [ Int(f"end_{i}") for i in range(n) ]

    # Add constraints for each meeting regarding timing and scheduling.
    for i, meeting in enumerate(meetings):
        # If the meeting is scheduled, then its start time must be no earlier than its available start,
        # and the meeting must finish by its available end. We set the meeting duration to be exactly the minimum.
        opt.add(Implies(scheduled[i],
                        And(
                            start_vars[i] >= meeting["avail_start"],
                            start_vars[i] <= meeting["avail_end"] - meeting["min_duration"],
                            end_vars[i] == start_vars[i] + meeting["min_duration"]
                        )))
        # If not scheduled, force the order to be 0.
        opt.add(Implies(Not(scheduled[i]), order_vars[i] == 0))
        # If scheduled, the order must be greater than 0 and at most n.
        opt.add(Implies(scheduled[i], And(order_vars[i] > 0, order_vars[i] <= n)))
    
    # Uniqueness: For any two scheduled meetings, their orders must be different.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))
    
    # Introduce an auxiliary variable max_order representing the number of scheduled meetings.
    max_order = Int("max_order")
    opt.add(max_order == Sum([If(scheduled[i], 1, 0) for i in range(n)]))
    for i in range(n):
        opt.add(Implies(scheduled[i], order_vars[i] <= max_order))
    
    # Enforce contiguity: For every integer k from 1 to n, if k <= max_order then some meeting has order k.
    for k in range(1, n+1):
        opt.add(Implies(k <= max_order, Or([And(scheduled[i], order_vars[i] == k) for i in range(n)])))
    
    # Add ordering constraints for consecutive meetings.
    # For meetings i and j, if meeting j is scheduled immediately after meeting i, then
    # meeting j's start time must be at least meeting i's end time plus the travel time from meeting i's location to j's location.
    for i in range(n):
        for j in range(n):
            if i != j:
                opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[j] == order_vars[i] + 1),
                                  start_vars[j] >= end_vars[i] + travel[meetings[i]["location"]][meetings[j]["location"]]))
    
    # For the first scheduled meeting (order==1), ensure that you can travel from the starting location, Marina District, which you reach at 9:00 (540 minutes).
    for i in range(n):
        opt.add(Implies(And(scheduled[i], order_vars[i] == 1),
                        start_vars[i] >= 540 + travel["Marina District"][meetings[i]["location"]]))
    
    # Objective: maximize the number of scheduled meetings (i.e., meet as many friends as possible).
    total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    # Check for a solution and extract the model.
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled_meetings = []
        for i in range(n):
            if model.evaluate(scheduled[i]):
                order_val = model.evaluate(order_vars[i]).as_long()
                st = model.evaluate(start_vars[i]).as_long()
                et = model.evaluate(end_vars[i]).as_long()
                scheduled_meetings.append((order_val, meetings[i]["location"], meetings[i]["person"], st, et))
        # Sort meetings by their order.
        scheduled_meetings.sort(key=lambda x: x[0])
        for om in scheduled_meetings:
            _, location, person, st, et = om
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(st),
                "end_time": minutes_to_time(et)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
    
if __name__ == "__main__":
    main()