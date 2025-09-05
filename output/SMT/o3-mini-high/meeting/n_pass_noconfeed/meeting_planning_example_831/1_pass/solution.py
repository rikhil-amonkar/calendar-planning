from z3 import *
import json

def minutes_to_time(m):
    # Converts integer minutes since midnight to a time string "H:MM" (24-hour, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Friend meeting parameters
    # Note: All meeting start times must be no earlier than 9:00 (i.e. 540 minutes)
    friends = [
        {"name": "Jeffrey", "location": "Fisherman's Wharf", "avail_start": 615, "avail_end": 780, "duration": 90},
        {"name": "Ronald", "location": "Alamo Square",      "avail_start": 540, "avail_end": 885, "duration": 120},
        {"name": "Jason", "location": "Financial District", "avail_start": 645, "avail_end": 960, "duration": 105},
        {"name": "Melissa", "location": "Union Square",      "avail_start": 1065, "avail_end": 1095, "duration": 15},
        {"name": "Elizabeth", "location": "Sunset District",   "avail_start": 885, "avail_end": 1050, "duration": 105},
        {"name": "Margaret", "location": "Embarcadero",       "avail_start": 795, "avail_end": 1140, "duration": 90},
        {"name": "George", "location": "Golden Gate Park",    "avail_start": 1140, "avail_end": 1320, "duration": 75},
        {"name": "Richard", "location": "Chinatown",          "avail_start": 570, "avail_end": 1260, "duration": 15},
        {"name": "Laura", "location": "Richmond District",    "avail_start": 585, "avail_end": 1080, "duration": 60},
    ]
    M = len(friends)

    # Travel times (in minutes) between locations (and from Presidio)
    travel = {
        "Presidio": {
            "Fisherman's Wharf": 19, "Alamo Square": 19, "Financial District": 23,
            "Union Square": 22, "Sunset District": 15, "Embarcadero": 20,
            "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7
        },
        "Fisherman's Wharf": {
            "Presidio": 17, "Alamo Square": 21, "Financial District": 11,
            "Union Square": 13, "Sunset District": 27, "Embarcadero": 8,
            "Golden Gate Park": 25, "Chinatown": 12, "Richmond District": 18
        },
        "Alamo Square": {
            "Presidio": 17, "Fisherman's Wharf": 19, "Financial District": 17,
            "Union Square": 14, "Sunset District": 16, "Embarcadero": 16,
            "Golden Gate Park": 9, "Chinatown": 15, "Richmond District": 11
        },
        "Financial District": {
            "Presidio": 22, "Fisherman's Wharf": 10, "Alamo Square": 17,
            "Union Square": 9, "Sunset District": 30, "Embarcadero": 4,
            "Golden Gate Park": 23, "Chinatown": 5, "Richmond District": 21
        },
        "Union Square": {
            "Presidio": 24, "Fisherman's Wharf": 15, "Alamo Square": 15,
            "Financial District": 9, "Sunset District": 27, "Embarcadero": 11,
            "Golden Gate Park": 22, "Chinatown": 7, "Richmond District": 20
        },
        "Sunset District": {
            "Presidio": 16, "Fisherman's Wharf": 29, "Alamo Square": 17,
            "Financial District": 30, "Union Square": 30, "Embarcadero": 30,
            "Golden Gate Park": 11, "Chinatown": 30, "Richmond District": 12
        },
        "Embarcadero": {
            "Presidio": 20, "Fisherman's Wharf": 6, "Alamo Square": 19,
            "Financial District": 5, "Union Square": 10, "Sunset District": 30,
            "Golden Gate Park": 25, "Chinatown": 7, "Richmond District": 21
        },
        "Golden Gate Park": {
            "Presidio": 11, "Fisherman's Wharf": 24, "Alamo Square": 9,
            "Financial District": 26, "Union Square": 22, "Sunset District": 10,
            "Embarcadero": 25, "Chinatown": 23, "Richmond District": 7
        },
        "Chinatown": {
            "Presidio": 19, "Fisherman's Wharf": 8, "Alamo Square": 17,
            "Financial District": 5, "Union Square": 7, "Sunset District": 29,
            "Embarcadero": 5, "Golden Gate Park": 23, "Richmond District": 20
        },
        "Richmond District": {
            "Presidio": 7, "Fisherman's Wharf": 18, "Alamo Square": 13,
            "Financial District": 22, "Union Square": 21, "Sunset District": 12,
            "Embarcadero": 19, "Golden Gate Park": 9, "Chinatown": 20
        },
    }

    # Create an Optimize object
    opt = Optimize()

    # For each friend we create variables:
    #  s_i: meeting start time (minutes since midnight)
    #  e_i: meeting end time (= s_i + duration if meeting is scheduled)
    #  order_i: an integer representing the position of this meeting in the itinerary
    #  attend_i: Boolean variable indicating whether we schedule a meeting with this friend.
    s_vars = [Int(f"s_{i}") for i in range(M)]
    e_vars = [Int(f"e_{i}") for i in range(M)]
    order_vars = [Int(f"order_{i}") for i in range(M)]
    attend_vars = [Bool(f"attend_{i}") for i in range(M)]

    # Add constraints for each friend if they are attended.
    # Note: Even if a friend’s original avail_start is earlier than 9:00, we force s_i >= 9:00.
    for i, f in enumerate(friends):
        effective_start = f["avail_start"] if f["avail_start"] >= 540 else 540
        opt.add(Implies(attend_vars[i], s_vars[i] >= effective_start))
        opt.add(Implies(attend_vars[i], e_vars[i] == s_vars[i] + f["duration"]))
        opt.add(Implies(attend_vars[i], e_vars[i] <= f["avail_end"]))
        # If not attended, fix times and order to 0 and M (an out-of-range marker)
        opt.add(Implies(Not(attend_vars[i]), s_vars[i] == 0))
        opt.add(Implies(Not(attend_vars[i]), e_vars[i] == 0))
        opt.add(Implies(attend_vars[i], And(order_vars[i] >= 0, order_vars[i] < M)))
        opt.add(Implies(Not(attend_vars[i]), order_vars[i] == M))

    # Enforce that any two attended meetings have distinct order values.
    for i in range(M):
        for j in range(i+1, M):
            opt.add(Implies(And(attend_vars[i], attend_vars[j]), order_vars[i] != order_vars[j]))

    # Only impose travel (consecutive) constraints between meetings that are immediately consecutive in the itinerary.
    # If friend j is scheduled immediately after friend i, then:
    #    s_j >= e_i + travel_time( i.location, j.location )
    for i in range(M):
        for j in range(M):
            opt.add(Implies(And(attend_vars[i], attend_vars[j], order_vars[j] == order_vars[i] + 1),
                            s_vars[j] >= e_vars[i] + travel[friends[i]["location"]][friends[j]["location"]]))

    # Enforce that the ordering is contiguous.
    # For every attended meeting with order > 0, there must be some attended meeting with order exactly one less.
    for i in range(M):
        opt.add(Implies(And(attend_vars[i], order_vars[i] > 0),
                        Or([And(attend_vars[j], order_vars[j] == order_vars[i] - 1) for j in range(M) if j != i])))

    # For the very first meeting in the itinerary (order 0), ensure that we can get there from Presidio.
    for i in range(M):
        opt.add(Implies(And(attend_vars[i], order_vars[i] == 0),
                        s_vars[i] >= 540 + travel["Presidio"][friends[i]["location"]]))

    # Objective: maximize the total number of meetings attended.
    total_attend = Sum([If(attend_vars[i], 1, 0) for i in range(M)])
    opt.maximize(total_attend)

    # Check and retrieve a solution if one exists.
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for i in range(M):
            if is_true(model.evaluate(attend_vars[i])):
                order_val = model.evaluate(order_vars[i]).as_long()
                start_val = model.evaluate(s_vars[i]).as_long()
                end_val = model.evaluate(e_vars[i]).as_long()
                schedule.append((order_val, i, start_val, end_val))
        schedule.sort(key=lambda x: x[0])
        itinerary = []
        for order_val, i, start_val, end_val in schedule:
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()