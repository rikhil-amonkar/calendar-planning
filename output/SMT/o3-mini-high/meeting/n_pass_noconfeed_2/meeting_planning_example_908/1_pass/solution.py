from z3 import *
import json

def minutes_to_time_str(m):
    # convert minutes (from midnight) to "H:MM" format (24-hour, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times dictionary (in minutes), using the exact values given.
    travel_times = {
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Sunset District"): 23,
        
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Sunset District"): 23,
        
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Sunset District"): 17,
        
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Sunset District"): 11,
        
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Sunset District"): 27,
        
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Union Square"): 30,
    }
    
    # Define friends and their meeting constraints (times in minutes after midnight)
    # 9:00 AM is 540 minutes.
    friends = [
        {
            "name": "Mark",
            "location": "Fisherman's Wharf",
            "start": 8 * 60 + 15,   # 8:15
            "end": 10 * 60,         # 10:00
            "min_dur": 30
        },
        {
            "name": "Stephanie",
            "location": "Presidio",
            "start": 12 * 60 + 15,  # 12:15
            "end": 15 * 60,         # 15:00
            "min_dur": 75
        },
        {
            "name": "Betty",
            "location": "Bayview",
            "start": 7 * 60 + 15,   # 7:15
            "end": 20 * 60 + 30,    # 20:30
            "min_dur": 15
        },
        {
            "name": "Lisa",
            "location": "Haight-Ashbury",
            "start": 15 * 60 + 30,  # 15:30
            "end": 18 * 60 + 30,    # 18:30
            "min_dur": 45
        },
        {
            "name": "William",
            "location": "Russian Hill",
            "start": 18 * 60 + 45,  # 18:45
            "end": 20 * 60,         # 20:00
            "min_dur": 60
        },
        {
            "name": "Brian",
            "location": "The Castro",
            "start": 9 * 60 + 15,   # 9:15
            "end": 13 * 60 + 15,    # 13:15
            "min_dur": 30
        },
        {
            "name": "Joseph",
            "location": "Marina District",
            "start": 10 * 60 + 45,  # 10:45
            "end": 15 * 60,         # 15:00
            "min_dur": 90
        },
        {
            "name": "Ashley",
            "location": "Richmond District",
            "start": 9 * 60 + 45,   # 9:45
            "end": 11 * 60 + 15,    # 11:15
            "min_dur": 45
        },
        {
            "name": "Patricia",
            "location": "Union Square",
            "start": 16 * 60 + 30,  # 16:30
            "end": 20 * 60,         # 20:00
            "min_dur": 120
        },
        {
            "name": "Karen",
            "location": "Sunset District",
            "start": 16 * 60 + 30,  # 16:30
            "end": 22 * 60,         # 22:00
            "min_dur": 105
        }
    ]
    
    n = len(friends)
    
    # Create an Optimize object
    opt = Optimize()
    
    # Decision variables for each friend
    selected = [Bool(f"sel_{i}") for i in range(n)]
    meeting_start = [Int(f"start_{i}") for i in range(n)]
    meeting_end = [Int(f"end_{i}") for i in range(n)]
    order = [Int(f"order_{i}") for i in range(n)]
    
    # Add constraints for each friend if selected:
    for i, friend in enumerate(friends):
        # If selected then meeting must occur within friend's availability and last for minimum duration.
        opt.add(If(selected[i],
                   And(meeting_start[i] >= friend["start"],
                       meeting_end[i] <= friend["end"],
                       meeting_end[i] - meeting_start[i] >= friend["min_dur"],
                       meeting_end[i] > meeting_start[i]),
                   True))
        # Order: if selected then order[i] > 0; if not selected then order[i] == 0.
        opt.add(If(selected[i], order[i] > 0, order[i] == 0))
        # Also, restrict order to be between 0 and n.
        opt.add(And(order[i] >= 0, order[i] <= n))
    
    # Distinct order numbers for selected meetings.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(selected[i], selected[j]), order[i] != order[j]))
    
    # If a meeting is the first in the sequence, account for travel from the starting point.
    # You arrive at Financial District at 9:00 (540 minutes).
    for i, friend in enumerate(friends):
        travel_from_fd = travel_times[("Financial District", friend["location"])]
        opt.add(Implies(And(selected[i], order[i] == 1),
                        meeting_start[i] >= 540 + travel_from_fd))
    
    # For any two meetings that are consecutive in the order, enforce travel time constraints.
    for i in range(n):
        for j in range(n):
            if i != j:
                # travel time from friend i's location to friend j's location
                if (friends[i]["location"], friends[j]["location"]) in travel_times:
                    t_time = travel_times[(friends[i]["location"], friends[j]["location"])]
                    opt.add(Implies(And(selected[i], selected[j], order[j] == order[i] + 1),
                                    meeting_start[j] >= meeting_end[i] + t_time))
    
    # Enforce contiguity of order numbers.
    total_meetings_expr = Sum([If(selected[i], 1, 0) for i in range(n)])
    for k in range(1, n+1):
        # For each k, if total meetings scheduled is at least k, then exactly one meeting gets order k; otherwise none.
        opt.add(If(total_meetings_expr >= k,
                   Sum([If(order[i] == k, 1, 0) for i in range(n)]) == 1,
                   Sum([If(order[i] == k, 1, 0) for i in range(n)]) == 0))
    
    # Objective: maximize the number of meetings scheduled.
    opt.maximize(total_meetings_expr)
    
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        # Collect scheduled meetings along with their order numbers
        scheduled_meetings = []
        for i in range(n):
            if is_true(model.evaluate(selected[i])):
                ord_val = model.evaluate(order[i]).as_long()
                st = model.evaluate(meeting_start[i]).as_long()
                en = model.evaluate(meeting_end[i]).as_long()
                scheduled_meetings.append((ord_val, friends[i]["name"], friends[i]["location"], st, en))
        # Sort meetings by order
        scheduled_meetings.sort(key=lambda x: x[0])
        for ord_val, name, location, st, en in scheduled_meetings:
            schedule.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time_str(st),
                "end_time": minutes_to_time_str(en)
            })
        result = {"itinerary": schedule}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
        
if __name__ == "__main__":
    main()