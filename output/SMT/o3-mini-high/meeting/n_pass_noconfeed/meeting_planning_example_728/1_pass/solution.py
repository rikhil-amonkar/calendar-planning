import json
from z3 import *

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Define travel times (in minutes) between locations.
    travel_times = {
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Russian Hill"): 15,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Russian Hill"): 24,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Haight-Ashbury"): 17
    }
    
    # Friend meeting data.
    # Times are represented as minutes from midnight.
    friends = [
        {"person": "Karen", "location": "Mission District", "avail_start": 14*60 + 15, "avail_end": 22*60 + 0, "min_duration": 30},
        {"person": "Richard", "location": "Fisherman's Wharf", "avail_start": 14*60 + 30, "avail_end": 17*60 + 30, "min_duration": 30},
        {"person": "Robert", "location": "Presidio", "avail_start": 21*60 + 45, "avail_end": 22*60 + 45, "min_duration": 60},
        {"person": "Joseph", "location": "Union Square", "avail_start": 11*60 + 45, "avail_end": 14*60 + 45, "min_duration": 120},
        {"person": "Helen", "location": "Sunset District", "avail_start": 14*60 + 45, "avail_end": 20*60 + 45, "min_duration": 105},
        {"person": "Elizabeth", "location": "Financial District", "avail_start": 10*60 + 0, "avail_end": 12*60 + 45, "min_duration": 75},
        {"person": "Kimberly", "location": "Haight-Ashbury", "avail_start": 14*60 + 15, "avail_end": 17*60 + 30, "min_duration": 105},
        {"person": "Ashley", "location": "Russian Hill", "avail_start": 11*60 + 30, "avail_end": 21*60 + 30, "min_duration": 45}
    ]
    
    N = len(friends)
    
    # Create an Optimize solver instance.
    opt = Optimize()
    
    # Decision variables for each friend meeting.
    meets = [Bool(f"meet_{i}") for i in range(N)]
    starts = [Int(f"start_{i}") for i in range(N)]
    ends = [Int(f"end_{i}") for i in range(N)]
    orders = [Int(f"order_{i}") for i in range(N)]
    
    # Total meetings scheduled (to be maximized).
    total_meetings = Int("total_meetings")
    opt.add(total_meetings == Sum([If(meets[i], 1, 0) for i in range(N)]))
    
    # For each potential meeting, add time window, duration, and order constraints.
    for i in range(N):
        f = friends[i]
        opt.add(Implies(meets[i], starts[i] >= f["avail_start"]))
        opt.add(Implies(meets[i], ends[i] <= f["avail_end"]))
        opt.add(Implies(meets[i], ends[i] - starts[i] >= f["min_duration"]))
        # Order variable: if meeting is scheduled it must be between 0 and 7; if not scheduled, it is -1.
        opt.add(Implies(meets[i], And(orders[i] >= 0, orders[i] < 8)))
        opt.add(Implies(Not(meets[i]), orders[i] == -1))
        # Ensure start and end are nonnegative when meeting takes place.
        opt.add(Implies(meets[i], starts[i] >= 0))
        opt.add(Implies(meets[i], ends[i] >= 0))
        # If scheduled, the order must be less than the total number of meetings.
        opt.add(Implies(meets[i], orders[i] < total_meetings))
    
    # For each order value from 0 to 7, if that order is less than total_meetings,
    # then some meeting must take that order.
    for r in range(8):
        opt.add(Implies(IntVal(r) < total_meetings, Or([And(meets[i], orders[i] == r) for i in range(N)])))
    
    # Uniqueness: any two scheduled meetings must have distinct order values.
    for i in range(N):
        for j in range(i+1, N):
            opt.add(Implies(And(meets[i], meets[j]), orders[i] != orders[j]))
    
    # Travel constraints: For any two meetings that are consecutive in the schedule,
    # ensure that the start time of the later meeting allows for travel from the earlier one.
    for i in range(N):
        for j in range(N):
            if i != j:
                from_loc = friends[i]["location"]
                to_loc = friends[j]["location"]
                travel_time_val = travel_times[(from_loc, to_loc)]
                opt.add(Implies(And(meets[i], meets[j], orders[j] == orders[i] + 1),
                                starts[j] >= ends[i] + travel_time_val))
    
    # For the first meeting in the schedule, account for travel from Marina District (arrival at 9:00 AM which is 540 minutes).
    for i in range(N):
        from_loc = "Marina District"
        to_loc = friends[i]["location"]
        travel_time_val = travel_times[(from_loc, to_loc)]
        opt.add(Implies(And(meets[i], orders[i] == 0),
                        starts[i] >= 540 + travel_time_val))
    
    # Objective: maximize the number of meetings scheduled.
    opt.maximize(total_meetings)
    
    # Solve and extract the schedule.
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled = []
        for i in range(N):
            if model.evaluate(meets[i]):
                order_val = model.evaluate(orders[i]).as_long()
                start_val = model.evaluate(starts[i]).as_long()
                end_val = model.evaluate(ends[i]).as_long()
                scheduled.append((order_val, friends[i]["person"], friends[i]["location"], start_val, end_val))
        # Sort the scheduled meetings by their order in the plan.
        scheduled.sort(key=lambda x: x[0])
        for s in scheduled:
            itinerary.append({
                "action": "meet",
                "person": s[1],
                "location": s[2],
                "start_time": format_time(s[3]),
                "end_time": format_time(s[4])
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()