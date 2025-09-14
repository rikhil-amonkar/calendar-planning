from z3 import *
import json

def format_time(t):
    # t is an integer representing minutes from midnight
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()
    
    # Travel times (in minutes) between locations.
    travel = {
        "Nob Hill": {
            "Richmond District": 14,
            "Financial District": 9,
            "North Beach": 8,
            "The Castro": 17,
            "Golden Gate Park": 17
        },
        "Richmond District": {
            "Nob Hill": 17,
            "Financial District": 22,
            "North Beach": 17,
            "The Castro": 16,
            "Golden Gate Park": 9
        },
        "Financial District": {
            "Nob Hill": 8,
            "Richmond District": 21,
            "North Beach": 7,
            "The Castro": 23,
            "Golden Gate Park": 23
        },
        "North Beach": {
            "Nob Hill": 7,
            "Richmond District": 18,
            "Financial District": 8,
            "The Castro": 22,
            "Golden Gate Park": 22
        },
        "The Castro": {
            "Nob Hill": 16,
            "Richmond District": 16,
            "Financial District": 20,
            "North Beach": 20,
            "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Nob Hill": 20,
            "Richmond District": 7,
            "Financial District": 26,
            "North Beach": 24,
            "The Castro": 13
        }
    }
    
    # Friend meeting constraints:
    # Times are in minutes from midnight.
    # Arrival at Nob Hill is at 9:00 AM -> 540 minutes.
    # Friend availability windows and required meeting durations:
    # Emily: Richmond District, available 19:00 (1140) to 21:00 (1260), min duration 15.
    # Margaret: Financial District, available 16:30 (990) to 20:15 (1215), min duration 75.
    # Ronald: North Beach, available 18:30 (1110) to 19:30 (1170), min duration 45.
    # Deborah: The Castro, available 13:45 (825) to 21:15 (1275), min duration 90.
    # Jeffrey: Golden Gate Park, available 11:15 (675) to 14:30 (870), min duration 120.
    friends = [
        {"name": "Emily", "location": "Richmond District", "avail_start": 19*60, "avail_end": 21*60, "duration": 15},
        {"name": "Margaret", "location": "Financial District", "avail_start": 16*60 + 30, "avail_end": 20*60 + 15, "duration": 75},
        {"name": "Ronald", "location": "North Beach", "avail_start": 18*60 + 30, "avail_end": 19*60 + 30, "duration": 45},
        {"name": "Deborah", "location": "The Castro", "avail_start": 13*60 + 45, "avail_end": 21*60 + 15, "duration": 90},
        {"name": "Jeffrey", "location": "Golden Gate Park", "avail_start": 11*60 + 15, "avail_end": 14*60 + 30, "duration": 120}
    ]
    n = len(friends)
    
    # Decision variables for each friend's meeting.
    # scheduled[i] indicates if the meeting with friend i is scheduled.
    # start[i] and end[i] denote the start and end time (in minutes from midnight) of the meeting.
    # order[i] is an integer representing the meeting's position in the schedule (1 = first, 2 = second, etc.).
    scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    order = [Int(f"order_{i}") for i in range(n)]
    
    # For each friend, if the meeting is scheduled then it must:
    # - Occur within the friend's available window.
    # - Last at least the required minimum duration.
    # If not scheduled, we set start and end to 0 and order to 0.
    for i in range(n):
        f = friends[i]
        opt.add(Implies(scheduled[i],
                        And(
                            start[i] >= f["avail_start"],
                            end[i] <= f["avail_end"],
                            end[i] - start[i] >= f["duration"],
                            start[i] < end[i]
                        )))
        opt.add(Implies(Not(scheduled[i]),
                        And(start[i] == 0, end[i] == 0)))
        # If scheduled, order is between 1 and n; otherwise, order is 0.
        opt.add(Implies(scheduled[i], And(order[i] >= 1, order[i] <= n)))
        opt.add(Implies(Not(scheduled[i]), order[i] == 0))
    
    # For any two scheduled meetings, they must have distinct order numbers.
    for i in range(n):
        for j in range(i + 1, n):
            opt.add(Implies(And(scheduled[i], scheduled[j]), order[i] != order[j]))
    
    # Ordering constraints:
    # If meeting i comes before meeting j (i.e., order[i] < order[j]), then you must have enough time
    # to travel from friend i's location to friend j's location.
    for i in range(n):
        for j in range(n):
            if i != j:
                loc_i = friends[i]["location"]
                loc_j = friends[j]["location"]
                travel_ij = travel[loc_i][loc_j]
                opt.add(Implies(And(scheduled[i], scheduled[j], order[i] < order[j]),
                                end[i] + travel_ij <= start[j]))
    
    # For the first meeting in the schedule, ensure you can travel from Nob Hill (arrival at 9:00 AM, 540 minutes)
    # to the meeting location.
    for i in range(n):
        loc = friends[i]["location"]
        travel_from_nob = travel["Nob Hill"][loc]
        opt.add(Implies(And(scheduled[i], order[i] == 1),
                        540 + travel_from_nob <= start[i]))
    
    # Objective: maximize the number of scheduled meetings.
    total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        # Extract scheduled meetings and sort them by their order value.
        meetings = []
        for i in range(n):
            if is_true(model.evaluate(scheduled[i])):
                o = model.evaluate(order[i]).as_long()
                s_time = model.evaluate(start[i]).as_long()
                e_time = model.evaluate(end[i]).as_long()
                meetings.append((o, friends[i]["name"], friends[i]["location"], s_time, e_time))
        meetings.sort(key=lambda x: x[0])
        
        itinerary = []
        for m in meetings:
            itinerary.append({
                "action": "meet",
                "location": m[2],
                "person": m[1],
                "start_time": format_time(m[3]),
                "end_time": format_time(m[4])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()