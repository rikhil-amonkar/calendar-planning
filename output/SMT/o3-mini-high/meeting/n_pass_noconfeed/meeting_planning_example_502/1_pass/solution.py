from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Friend meeting data
    # Times are in minutes from midnight.
    friends = [
        {"name": "Stephanie", "location": "Golden Gate Park", "avail_start": 660, "avail_end": 900, "min_duration": 105},
        {"name": "Karen",     "location": "Chinatown",         "avail_start": 825, "avail_end": 990, "min_duration": 15},
        {"name": "Brian",     "location": "Union Square",      "avail_start": 900, "avail_end": 1035, "min_duration": 30},
        {"name": "Rebecca",   "location": "Fisherman's Wharf", "avail_start": 480, "avail_end": 675, "min_duration": 30},
        {"name": "Joseph",    "location": "Pacific Heights",   "avail_start": 495, "avail_end": 570, "min_duration": 60},
        {"name": "Steven",    "location": "North Beach",       "avail_start": 870, "avail_end": 1245, "min_duration": 120}
    ]
    
    # Travel times in minutes between locations.
    # Note: The travel times are not necessarily symmetric.
    travel = {
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "North Beach"): 7,
        
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "North Beach"): 24,
        
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "North Beach"): 3,
        
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "North Beach"): 10,
        
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "North Beach"): 6,
        
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "North Beach"): 9,
        
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Pacific Heights"): 8,
    }
    
    # Starting point details
    FD_location = "Financial District"
    FD_start_time = 540  # 9:00 AM
    
    opt = Optimize()

    # Create decision variables for each friend.
    attend = {}
    start_time_vars = {}
    end_time_vars = {}
    order_vars = {}
    for friend in friends:
        name = friend["name"]
        attend[name] = Bool("attend_" + name)
        start_time_vars[name] = Int("start_" + name)
        end_time_vars[name] = Int("end_" + name)
        order_vars[name] = Int("order_" + name)
        
    # total_meet will count the number of meetings attended.
    names = [friend["name"] for friend in friends]
    total_meet = Int("total_meet")
    opt.add(total_meet == Sum([If(attend[n], 1, 0) for n in names]))
    
    # For each friend, if the meeting is scheduled, enforce time window and minimum meeting duration.
    for friend in friends:
        name = friend["name"]
        avail_start = friend["avail_start"]
        avail_end = friend["avail_end"]
        min_dur = friend["min_duration"]
        # If meeting is scheduled, meeting start must be within availability and the duration must be met.
        opt.add(Implies(attend[name],
                        And(start_time_vars[name] >= avail_start,
                            start_time_vars[name] <= avail_end,
                            end_time_vars[name] <= avail_end,
                            end_time_vars[name] - start_time_vars[name] >= min_dur)))
        # If meeting is scheduled, its order must be between 0 and 5.
        opt.add(Implies(attend[name], And(order_vars[name] >= 0, order_vars[name] < 6)))
        # If meeting is not scheduled, set its order to a dummy value 6.
        opt.add(Implies(Not(attend[name]), order_vars[name] == 6))
        # Also, if scheduled, the order must be less than the total number of meetings.
        opt.add(Implies(attend[name], order_vars[name] < total_meet))
    
    # Ensure that scheduled meetings get distinct order numbers.
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            opt.add(Implies(And(attend[names[i]], attend[names[j]]),
                            order_vars[names[i]] != order_vars[names[j]]))
    
    # For the first meeting in the schedule (order 0), ensure we can travel from the Financial District.
    for friend in friends:
        name = friend["name"]
        loc = friend["location"]
        t = travel[(FD_location, loc)]
        opt.add(Implies(And(attend[name], order_vars[name] == 0),
                        start_time_vars[name] >= FD_start_time + t))
    
    # For every meeting that is not the first, ensure that its immediate predecessor in the order is connected by travel.
    # For each meeting j, if it is scheduled and its order is > 0, then there must be some meeting i
    # such that i is scheduled, order[i] == order[j] - 1, and travel from i to j is feasible.
    for friend_j in friends:
        name_j = friend_j["name"]
        disjuncts = []
        for friend_i in friends:
            name_i = friend_i["name"]
            if name_i == name_j:
                continue
            travel_time_ij = travel[(friend_i["location"], friend_j["location"])]
            disjuncts.append(And(attend[name_i],
                                 order_vars[name_i] == order_vars[name_j] - 1,
                                 end_time_vars[name_i] + travel_time_ij <= start_time_vars[name_j]))
        # If meeting j is scheduled and not first, at least one predecessor must satisfy the travel constraint.
        if disjuncts:
            opt.add(Implies(And(attend[name_j], order_vars[name_j] > 0), Or(disjuncts)))
    
    # Objective: maximize the number of meetings attended.
    opt.maximize(total_meet)
    
    # Solve and extract the itinerary.
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        scheduled = []
        for friend in friends:
            name = friend["name"]
            if m.evaluate(attend[name]):
                order_val = m.evaluate(order_vars[name]).as_long()
                st = m.evaluate(start_time_vars[name]).as_long()
                et = m.evaluate(end_time_vars[name]).as_long()
                scheduled.append((order_val, name, friend["location"], st, et))
        scheduled.sort(key=lambda x: x[0])
        for order_val, name, loc, st, et in scheduled:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_time(st),
                "end_time": minutes_to_time(et)
            })
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()