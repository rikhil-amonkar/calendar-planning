from z3 import *
import json

def minute_to_time_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times in minutes as provided
    travel = {}
    travel[("Presidio", "Pacific Heights")] = 11
    travel[("Presidio", "Golden Gate Park")] = 12
    travel[("Presidio", "Fisherman's Wharf")] = 19
    travel[("Presidio", "Marina District")] = 11
    travel[("Presidio", "Alamo Square")] = 19
    travel[("Presidio", "Sunset District")] = 15
    travel[("Presidio", "Nob Hill")] = 18
    travel[("Presidio", "North Beach")] = 18

    travel[("Pacific Heights", "Presidio")] = 11
    travel[("Pacific Heights", "Golden Gate Park")] = 15
    travel[("Pacific Heights", "Fisherman's Wharf")] = 13
    travel[("Pacific Heights", "Marina District")] = 6
    travel[("Pacific Heights", "Alamo Square")] = 10
    travel[("Pacific Heights", "Sunset District")] = 21
    travel[("Pacific Heights", "Nob Hill")] = 8
    travel[("Pacific Heights", "North Beach")] = 9

    travel[("Golden Gate Park", "Presidio")] = 11
    travel[("Golden Gate Park", "Pacific Heights")] = 16
    travel[("Golden Gate Park", "Fisherman's Wharf")] = 24
    travel[("Golden Gate Park", "Marina District")] = 16
    travel[("Golden Gate Park", "Alamo Square")] = 9
    travel[("Golden Gate Park", "Sunset District")] = 10
    travel[("Golden Gate Park", "Nob Hill")] = 20
    travel[("Golden Gate Park", "North Beach")] = 23

    travel[("Fisherman's Wharf", "Presidio")] = 17
    travel[("Fisherman's Wharf", "Pacific Heights")] = 12
    travel[("Fisherman's Wharf", "Golden Gate Park")] = 25
    travel[("Fisherman's Wharf", "Marina District")] = 9
    travel[("Fisherman's Wharf", "Alamo Square")] = 21
    travel[("Fisherman's Wharf", "Sunset District")] = 27
    travel[("Fisherman's Wharf", "Nob Hill")] = 11
    travel[("Fisherman's Wharf", "North Beach")] = 6

    travel[("Marina District", "Presidio")] = 10
    travel[("Marina District", "Pacific Heights")] = 7
    travel[("Marina District", "Golden Gate Park")] = 18
    travel[("Marina District", "Fisherman's Wharf")] = 10
    travel[("Marina District", "Alamo Square")] = 15
    travel[("Marina District", "Sunset District")] = 19
    travel[("Marina District", "Nob Hill")] = 12
    travel[("Marina District", "North Beach")] = 11

    travel[("Alamo Square", "Presidio")] = 17
    travel[("Alamo Square", "Pacific Heights")] = 10
    travel[("Alamo Square", "Golden Gate Park")] = 9
    travel[("Alamo Square", "Fisherman's Wharf")] = 19
    travel[("Alamo Square", "Marina District")] = 15
    travel[("Alamo Square", "Sunset District")] = 16
    travel[("Alamo Square", "Nob Hill")] = 11
    travel[("Alamo Square", "North Beach")] = 15

    travel[("Sunset District", "Presidio")] = 16
    travel[("Sunset District", "Pacific Heights")] = 21
    travel[("Sunset District", "Golden Gate Park")] = 11
    travel[("Sunset District", "Fisherman's Wharf")] = 29
    travel[("Sunset District", "Marina District")] = 21
    travel[("Sunset District", "Alamo Square")] = 17
    travel[("Sunset District", "Nob Hill")] = 27
    travel[("Sunset District", "North Beach")] = 28

    travel[("Nob Hill", "Presidio")] = 17
    travel[("Nob Hill", "Pacific Heights")] = 8
    travel[("Nob Hill", "Golden Gate Park")] = 17
    travel[("Nob Hill", "Fisherman's Wharf")] = 10
    travel[("Nob Hill", "Marina District")] = 11
    travel[("Nob Hill", "Alamo Square")] = 11
    travel[("Nob Hill", "Sunset District")] = 24
    travel[("Nob Hill", "North Beach")] = 8

    travel[("North Beach", "Presidio")] = 17
    travel[("North Beach", "Pacific Heights")] = 8
    travel[("North Beach", "Golden Gate Park")] = 22
    travel[("North Beach", "Fisherman's Wharf")] = 5
    travel[("North Beach", "Marina District")] = 9
    travel[("North Beach", "Alamo Square")] = 16
    travel[("North Beach", "Sunset District")] = 27
    travel[("North Beach", "Nob Hill")] = 7

    # Define meetings with their constraints.
    # Times are represented in minutes after midnight.
    meetings = [
        {"person": "Kevin", "location": "Pacific Heights", "avail_start": 7 * 60 + 15, "avail_end": 8 * 60 + 45, "min_duration": 90},
        {"person": "Michelle", "location": "Golden Gate Park", "avail_start": 20 * 60, "avail_end": 21 * 60, "min_duration": 15},
        {"person": "Emily", "location": "Fisherman's Wharf", "avail_start": 16 * 60 + 15, "avail_end": 19 * 60, "min_duration": 30},
        {"person": "Mark", "location": "Marina District", "avail_start": 18 * 60 + 15, "avail_end": 19 * 60 + 45, "min_duration": 75},
        {"person": "Barbara", "location": "Alamo Square", "avail_start": 17 * 60, "avail_end": 19 * 60, "min_duration": 120},
        {"person": "Laura", "location": "Sunset District", "avail_start": 19 * 60, "avail_end": 21 * 60 + 15, "min_duration": 75},
        {"person": "Mary", "location": "Nob Hill", "avail_start": 17 * 60 + 30, "avail_end": 19 * 60, "min_duration": 45},
        {"person": "Helen", "location": "North Beach", "avail_start": 11 * 60, "avail_end": 12 * 60 + 15, "min_duration": 45}
    ]

    n = len(meetings)
    # Create an Optimize solver which will allow us to maximize the number of meetings
    opt = Optimize()

    # Decision variables:
    # x[i]: whether meeting i is scheduled.
    # s_vars[i] and e_vars[i]: start and end times for meeting i (in minutes after midnight).
    # order_vars[i]: the order of meeting i in the itinerary. If not scheduled, order will be -1.
    x = [Bool(f"x_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]

    # Add constraints for each meeting (if scheduled, enforce availability and duration)
    for i in range(n):
        m_info = meetings[i]
        avail_start = m_info["avail_start"]
        avail_end = m_info["avail_end"]
        min_dur = m_info["min_duration"]

        # If the meeting is scheduled, then start and end times must be within available window and meet minimum duration.
        opt.add(Implies(x[i], s_vars[i] >= avail_start))
        opt.add(Implies(x[i], e_vars[i] <= avail_end))
        opt.add(Implies(x[i], e_vars[i] - s_vars[i] >= min_dur))
        opt.add(Implies(x[i], e_vars[i] >= s_vars[i]))

        # If scheduled, the order is between 0 and n-1; if not scheduled, order is -1.
        opt.add(Implies(x[i], And(order_vars[i] >= 0, order_vars[i] < n)))
        opt.add(Implies(Not(x[i]), order_vars[i] == -1))

    # Constraint for the first meeting in the itinerary:
    # For any meeting scheduled as the first one (order == 0), its start time must be at or after 9:00 (540 minutes)
    # plus the travel time from Presidio to its location.
    for i in range(n):
        location = meetings[i]["location"]
        travel_time = travel[("Presidio", location)]
        opt.add(Implies(And(x[i], order_vars[i] == 0), s_vars[i] >= 540 + travel_time))

    # Enforce that scheduled meetings have distinct order numbers.
    for i in range(n):
        for j in range(i + 1, n):
            opt.add(Implies(And(x[i], x[j]), order_vars[i] != order_vars[j]))

    # Enforce ordering and travel constraints between meetings:
    # If meeting i is scheduled before meeting j then the start time of j
    # must be at least the end time of i plus the travel time from i's location to j's location.
    for i in range(n):
        for j in range(n):
            if i != j:
                loc_i = meetings[i]["location"]
                loc_j = meetings[j]["location"]
                travel_time = travel[(loc_i, loc_j)]
                opt.add(Implies(And(x[i], x[j], order_vars[i] >= 0, order_vars[j] >= 0, order_vars[i] < order_vars[j]),
                                s_vars[j] >= e_vars[i] + travel_time))

    # Objective: maximize the total number of meetings scheduled.
    total_meetings = Sum([If(x[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    # Check for a solution and extract the model.
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(n):
            if model.evaluate(x[i]):
                order_val = model.evaluate(order_vars[i]).as_long()
                s_val = model.evaluate(s_vars[i]).as_long()
                e_val = model.evaluate(e_vars[i]).as_long()
                scheduled_meetings.append((order_val, meetings[i]["person"], meetings[i]["location"], s_val, e_val))
        scheduled_meetings.sort(key=lambda tup: tup[0])

        itinerary = []
        for order_val, person, location, s_time, e_time in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minute_to_time_str(s_time),
                "end_time": minute_to_time_str(e_time)
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()