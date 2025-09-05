from z3 import *
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()

    # Dummy meeting: starting point at Union Square, fixed at 9:00 AM (540 minutes)
    dummy_start = 540
    dummy_end = 540
    dummy_location = "Union Square"

    # Define friends, their meeting locations, availability windows, and minimum meeting durations.
    friends = ["Karen", "Joseph", "Sandra", "Nancy"]
    locations = {
        "Karen": "Nob Hill",
        "Joseph": "Haight-Ashbury",
        "Sandra": "Chinatown",
        "Nancy": "Marina District"
    }
    avail_start = {
        "Karen": 21 * 60 + 15,     # 21:15 -> 1275
        "Joseph": 12 * 60 + 30,    # 12:30 -> 750
        "Sandra": 7 * 60 + 15,     # 7:15  -> 435
        "Nancy": 11 * 60         ,# 11:00 -> 660
    }
    avail_end = {
        "Karen": 21 * 60 + 45,     # 21:45 -> 1305
        "Joseph": 19 * 60 + 45,    # 19:45 -> 1185
        "Sandra": 19 * 60 + 15,    # 19:15 -> 1155
        "Nancy": 20 * 60 + 15      # 20:15 -> 1215
    }
    durations = {
        "Karen": 30,
        "Joseph": 90,
        "Sandra": 75,
        "Nancy": 105
    }

    # Travel times between locations in minutes.
    travel = {
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Marina District"): 18,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Marina District"): 11,
        ("Haight-Ashbury", "Union Square"): 17,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Nob Hill"): 8,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Marina District"): 12,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Chinatown"): 16
    }

    # Decision variables for each meeting (if scheduled, start time, and end time)
    sched = {}
    start_vars = {}
    end_vars = {}

    for friend in friends:
        sched[friend] = Bool(f"sched_{friend}")
        start_vars[friend] = Int(f"start_{friend}")
        end_vars[friend] = Int(f"end_{friend}")
        # Compute the earliest possible arrival if going directly from the dummy (Union Square)
        direct_arrival = dummy_start + travel[(dummy_location, locations[friend])]
        # Lower bound on start time is the later of the friend's availability and direct arrival.
        lower_bound = avail_start[friend] if avail_start[friend] > direct_arrival else direct_arrival
        opt.add(Implies(sched[friend], start_vars[friend] >= lower_bound))
        opt.add(Implies(sched[friend], start_vars[friend] <= avail_end[friend] - durations[friend]))
        opt.add(Implies(sched[friend], end_vars[friend] <= avail_end[friend]))
        opt.add(Implies(sched[friend], end_vars[friend] - start_vars[friend] >= durations[friend]))
        # Ensure that even if not the first meeting, the meeting cannot start before it's reachable directly.
        opt.add(Implies(sched[friend], dummy_end + travel[(dummy_location, locations[friend])] <= start_vars[friend]))

    # For any two meetings that are scheduled, enforce a sequential order with the required travel time.
    n = len(friends)
    for i in range(n):
        for j in range(i+1, n):
            f_i = friends[i]
            f_j = friends[j]
            travel_i_j = travel[(locations[f_i], locations[f_j])]
            travel_j_i = travel[(locations[f_j], locations[f_i])]
            opt.add(Implies(And(sched[f_i], sched[f_j]),
                            Or(end_vars[f_i] + travel_i_j <= start_vars[f_j],
                               end_vars[f_j] + travel_j_i <= start_vars[f_i])))

    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(sched[f], 1, 0) for f in friends])
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled_meetings = []
        for friend in friends:
            if is_true(model.evaluate(sched[friend])):
                s_time = model.evaluate(start_vars[friend]).as_long()
                e_time = model.evaluate(end_vars[friend]).as_long()
                scheduled_meetings.append((s_time, friend, e_time))
        # Sort meetings by their start times.
        scheduled_meetings.sort(key=lambda x: x[0])
        for s_time, friend, e_time in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": locations[friend],
                "person": friend,
                "start_time": minutes_to_time(s_time),
                "end_time": minutes_to_time(e_time)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()