from z3 import *
import json

# Helper function to convert minutes (since midnight) to a "HH:MM" string.
def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def main():
    # Define each friend’s data:
    # Times are in minutes from midnight.
    # For example, 9:00AM = 540, 9:15AM = 555, 17:00 = 1020, etc.
    friends = ["Sarah", "Patricia", "Matthew", "Joseph", "Robert"]
    friend_data = {
        "Sarah":    {"location": "Haight-Ashbury",  "avail_start": 1020, "avail_end": 1290, "min_duration": 105},  # 17:00-21:30
        "Patricia": {"location": "Sunset District",   "avail_start": 1020, "avail_end": 1185, "min_duration": 45},   # 17:00-19:45
        "Matthew":  {"location": "Marina District",   "avail_start": 555,  "avail_end": 720,  "min_duration": 15},   # 9:15-12:00
        "Joseph":   {"location": "Financial District","avail_start": 855,  "avail_end": 1125, "min_duration": 30},   # 14:15-18:45
        "Robert":   {"location": "Union Square",      "avail_start": 615,  "avail_end": 1305, "min_duration": 15}    # 10:15-21:45
    }
    
    # Travel times (in minutes) between locations.
    # Note that times are not completely symmetric.
    travel = {
        "Golden Gate Park": {
            "Haight-Ashbury": 7,
            "Sunset District": 10,
            "Marina District": 16,
            "Financial District": 26,
            "Union Square": 22
        },
        "Haight-Ashbury": {
            "Golden Gate Park": 7,
            "Sunset District": 15,
            "Marina District": 17,
            "Financial District": 21,
            "Union Square": 17
        },
        "Sunset District": {
            "Golden Gate Park": 11,
            "Haight-Ashbury": 15,
            "Marina District": 21,
            "Financial District": 30,
            "Union Square": 30
        },
        "Marina District": {
            "Golden Gate Park": 18,
            "Haight-Ashbury": 16,
            "Sunset District": 19,
            "Financial District": 17,
            "Union Square": 16
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Haight-Ashbury": 19,
            "Sunset District": 31,
            "Marina District": 15,
            "Union Square": 9
        },
        "Union Square": {
            "Golden Gate Park": 22,
            "Haight-Ashbury": 18,
            "Sunset District": 26,
            "Marina District": 18,
            "Financial District": 9
        }
    }
    
    # Create an Optimize solver.
    opt = Optimize()
    
    # For each friend we create:
    #  - a start time and an end time for the meeting,
    #  - a Boolean variable indicating if we schedule the meeting (attend),
    #  - an integer order variable (nonzero if attended, 1 = first meeting, 2 = second, etc.)
    start_vars = {}
    end_vars = {}
    attend_vars = {}
    order_vars = {}
    N = len(friends)
    
    for f in friends:
        start_vars[f] = Int(f"start_{f}")
        end_vars[f]   = Int(f"end_{f}")
        attend_vars[f] = Bool(f"attend_{f}")
        order_vars[f] = Int(f"order_{f}")
        
        data = friend_data[f]
        # If we attend, then the meeting must lie within the friend’s available window...
        opt.add(Implies(attend_vars[f], start_vars[f] >= data["avail_start"]))
        opt.add(Implies(attend_vars[f], end_vars[f] <= data["avail_end"]))
        # ...and must last at least the minimum required duration.
        opt.add(Implies(attend_vars[f], end_vars[f] - start_vars[f] >= data["min_duration"]))
        # If not attended, then fix the order to 0.
        opt.add(Implies(Not(attend_vars[f]), order_vars[f] == 0))
        # If attended, order must be between 1 and N.
        opt.add(Implies(attend_vars[f], And(order_vars[f] >= 1, order_vars[f] <= N)))
    
    # For any two distinct attended meetings, their order numbers must differ.
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            f1 = friends[i]
            f2 = friends[j]
            opt.add(Implies(And(attend_vars[f1], attend_vars[f2]), order_vars[f1] != order_vars[f2]))
    
    # Add travel constraints for consecutive meetings.
    # If meeting f1 is immediately before meeting f2 (i.e. order[f2] == order[f1] + 1),
    # then we must allow enough travel time from f1’s location to f2’s location.
    for f1 in friends:
        for f2 in friends:
            if f1 != f2:
                tt = travel[ friend_data[f1]["location"] ][ friend_data[f2]["location"] ]
                opt.add(Implies(And(attend_vars[f1], attend_vars[f2], order_vars[f2] == order_vars[f1] + 1),
                                start_vars[f2] >= end_vars[f1] + tt))
    
    # The very first meeting must be reachable from Golden Gate Park (which we arrive at 9:00 = 540 minutes).
    for f in friends:
        tt = travel["Golden Gate Park"][ friend_data[f]["location"] ]
        opt.add(Implies(And(attend_vars[f], order_vars[f] == 1),
                        start_vars[f] >= 540 + tt))
    
    # (Optional) if one meeting is scheduled before another then its start time should be no later.
    for f1 in friends:
        for f2 in friends:
            if f1 != f2:
                opt.add(Implies(And(attend_vars[f1], attend_vars[f2], order_vars[f1] < order_vars[f2]),
                                 start_vars[f1] <= start_vars[f2]))
    
    # Our objective is to maximize the number of meetings attended.
    attend_sum = Sum([If(attend_vars[f], 1, 0) for f in friends])
    opt.maximize(attend_sum)
    
    # Check and solve.
    if opt.check() == sat:
        model = opt.model()
        # Build a list of scheduled meetings (only those where attend==True).
        scheduled = []
        for f in friends:
            if is_true(model.evaluate(attend_vars[f])):
                order_val = model.evaluate(order_vars[f]).as_long()
                s_val = model.evaluate(start_vars[f]).as_long()
                e_val = model.evaluate(end_vars[f]).as_long()
                scheduled.append((order_val, f, s_val, e_val))
        # Sort meetings by their order value.
        scheduled.sort(key=lambda x: x[0])
        itinerary = []
        for (_, person, s, e) in scheduled:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": minutes_to_time(s),
                "end_time": minutes_to_time(e)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No schedule found.")

if __name__ == '__main__':
    main()