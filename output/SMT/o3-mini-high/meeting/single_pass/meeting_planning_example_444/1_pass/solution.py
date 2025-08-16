from z3 import *

def main():
    # We'll measure time in minutes after 9:00.
    # Meeting data:
    #   avail_start and avail_end are in minutes relative to 9:00.
    #   duration is the minimum meeting duration.
    meetings = {
        "Patricia": { "loc": "Sunset",        "avail_start": 15,   "avail_end": 780, "duration": 60 },
        "Laura":    { "loc": "North Beach",   "avail_start": 210,  "avail_end": 225, "duration": 15 },
        "Ronald":   { "loc": "Russian Hill",  "avail_start": 285,  "avail_end": 495, "duration": 105 },
        "Emily":    { "loc": "The Castro",    "avail_start": 435,  "avail_end": 570, "duration": 60 },
        "Mary":     { "loc": "Golden Gate Park", "avail_start": 360, "avail_end": 450, "duration": 60 }
    }
    # Travel times (in minutes) between locations.
    # Times from "Financial District" (our starting location) to each meeting location:
    travel_times = {
        ("Financial District", "Sunset"): 31,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Russian Hill"): 10,
        ("Financial District", "The Castro"): 23,
        ("Financial District", "Golden Gate Park"): 23,
        # Between meeting locations (note: travel times are not fully symmetric)
        ("Sunset", "North Beach"): 29,
        ("Sunset", "Russian Hill"): 24,
        ("Sunset", "The Castro"): 17,
        ("Sunset", "Golden Gate Park"): 11,
        ("North Beach", "Sunset"): 27,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Golden Gate Park"): 22,
        ("Russian Hill", "Sunset"): 23,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("The Castro", "Sunset"): 17,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Sunset"): 10,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "The Castro"): 13,
    }

    opt = Optimize()

    # For each meeting we create three variables:
    #   attend: Bool; whether we decide to meet that friend.
    #   s: Int; start time of the meeting (in minutes after 9:00).
    #   order: Int; an integer ordering of the meeting (if attended) in our day.
    s = {}      # start times
    attend = {} # Boolean: did we meet this friend?
    order = {}  # order in the schedule (if attended, nonnegative; if not, set to -1)
    for person, data in meetings.items():
        attend[person] = Bool("attend_" + person)
        s[person] = Int("s_" + person)       # meeting start time (minutes after 9:00)
        order[person] = Int("order_" + person) # ordering position
        
        # If we attend, the meeting must start no earlier than its avail_start
        # and finish no later than avail_end.
        opt.add(If(attend[person],
                   And(s[person] >= data["avail_start"],
                       s[person] <= data["avail_end"] - data["duration"]),
                   s[person] == 0))  # if not attended, set start time arbitrarily to 0.
        
        # If attended, assign an order in {0,1,2,3,4}; if not, order will be -1.
        opt.add(If(attend[person],
                   And(order[person] >= 0, order[person] <= 4),
                   order[person] == -1))
    
    # Our goal is to maximize the number of friends met.
    total_attended = Sum([If(attend[p], 1, 0) for p in meetings])
    opt.maximize(total_attended)
    
    # For every two different meetings, if both are attended then one must come before the other.
    # And if meeting i comes before meeting j then the finish time of i plus travel time from i’s location to j’s location
    # must be no later than the start time of j.
    persons = list(meetings.keys())
    for i in range(len(persons)):
        for j in range(i+1, len(persons)):
            p_i = persons[i]
            p_j = persons[j]
            dur_i = meetings[p_i]["duration"]
            dur_j = meetings[p_j]["duration"]
            loc_i = meetings[p_i]["loc"]
            loc_j = meetings[p_j]["loc"]
            travel_i_j = travel_times[(loc_i, loc_j)]
            travel_j_i = travel_times[(loc_j, loc_i)]
            # If both meetings are attended then either p_i comes before p_j or vice‐versa.
            # Use an if-then-else to enforce the proper travel gap.
            opt.add(Implies(And(attend[p_i], attend[p_j]),
                If(order[p_i] < order[p_j],
                   s[p_i] + dur_i + travel_i_j <= s[p_j],
                   s[p_j] + dur_j + travel_j_i <= s[p_i]
                )
            ))
            # Also, if both are attended, they must have distinct order values.
            opt.add(Implies(And(attend[p_i], attend[p_j]), order[p_i] != order[p_j]))
    
    # Travel from starting location (Financial District) to the location of the first meeting.
    # For any meeting that is scheduled as the first one (order == 0), ensure that
    # the travel time from Financial District to its location is no more than its start time.
    for person, data in meetings.items():
        loc = data["loc"]
        travel_fd = travel_times[("Financial District", loc)]
        opt.add(Implies(And(attend[person], order[person] == 0), travel_fd <= s[person]))
    
    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        # Build a list of attended meetings, sorted by their order value.
        scheduled = []
        for person in persons:
            if is_true(model.evaluate(attend[person])):
                start_val = model.evaluate(s[person]).as_long()
                end_val = start_val + meetings[person]["duration"]
                order_val = model.evaluate(order[person]).as_long()
                scheduled.append((order_val, person, start_val, end_val))
        scheduled.sort(key=lambda x: x[0])
        
        # Convert minutes from 9:00 into a HH:MM string in 24-hour format.
        def convert_time(minutes):
            total_minutes = 9 * 60 + minutes
            hh = total_minutes // 60
            mm = total_minutes % 60
            return f"{hh:02d}:{mm:02d}"
        
        itinerary = []
        for order_val, person, start_val, end_val in scheduled:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": convert_time(start_val),
                "end_time": convert_time(end_val)
            })
        
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=4))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()