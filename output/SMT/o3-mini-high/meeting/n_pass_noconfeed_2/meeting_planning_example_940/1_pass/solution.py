from z3 import *
import json

def main():
    opt = Optimize()

    # Define friend meeting constraints.
    # Times are represented in minutes from midnight.
    # 9:00 AM is 540.
    friends = [
        {"name": "Kevin", "location": "Mission District", "avail_start": 1245, "avail_end": 1305, "min_duration": 60},
        {"name": "Mark", "location": "Fisherman's Wharf", "avail_start": 1035, "avail_end": 1200, "min_duration": 90},
        {"name": "Jessica", "location": "Russian Hill", "avail_start": 540, "avail_end": 900, "min_duration": 120},
        {"name": "Jason", "location": "Marina District", "avail_start": 915, "avail_end": 1305, "min_duration": 120},
        {"name": "John", "location": "North Beach", "avail_start": 585, "avail_end": 1080, "min_duration": 15},
        {"name": "Karen", "location": "Chinatown", "avail_start": 1005, "avail_end": 1140, "min_duration": 75},
        {"name": "Sarah", "location": "Pacific Heights", "avail_start": 1050, "avail_end": 1095, "min_duration": 45},
        {"name": "Amanda", "location": "The Castro", "avail_start": 1200, "avail_end": 1275, "min_duration": 60},
        {"name": "Nancy", "location": "Nob Hill", "avail_start": 585, "avail_end": 780, "min_duration": 45},
        {"name": "Rebecca", "location": "Sunset District", "avail_start": 525, "avail_end": 900, "min_duration": 75}
    ]
    N = len(friends)
    
    # Define travel times in minutes between locations.
    # Note: travel times are not symmetric in all cases.
    travel_times = {
        "Union Square": {
            "Mission District": 14,
            "Fisherman's Wharf": 15,
            "Russian Hill": 13,
            "Marina District": 18,
            "North Beach": 10,
            "Chinatown": 7,
            "Pacific Heights": 15,
            "The Castro": 17,
            "Nob Hill": 9,
            "Sunset District": 27,
        },
        "Mission District": {
            "Union Square": 15,
            "Fisherman's Wharf": 22,
            "Russian Hill": 15,
            "Marina District": 19,
            "North Beach": 17,
            "Chinatown": 16,
            "Pacific Heights": 16,
            "The Castro": 7,
            "Nob Hill": 12,
            "Sunset District": 24,
        },
        "Fisherman's Wharf": {
            "Union Square": 13,
            "Mission District": 22,
            "Russian Hill": 7,
            "Marina District": 9,
            "North Beach": 6,
            "Chinatown": 12,
            "Pacific Heights": 12,
            "The Castro": 27,
            "Nob Hill": 11,
            "Sunset District": 27,
        },
        "Russian Hill": {
            "Union Square": 10,
            "Mission District": 16,
            "Fisherman's Wharf": 7,
            "Marina District": 7,
            "North Beach": 5,
            "Chinatown": 9,
            "Pacific Heights": 7,
            "The Castro": 21,
            "Nob Hill": 5,
            "Sunset District": 23,
        },
        "Marina District": {
            "Union Square": 16,
            "Mission District": 20,
            "Fisherman's Wharf": 10,
            "Russian Hill": 8,
            "North Beach": 11,
            "Chinatown": 15,
            "Pacific Heights": 7,
            "The Castro": 22,
            "Nob Hill": 12,
            "Sunset District": 19,
        },
        "North Beach": {
            "Union Square": 7,
            "Mission District": 18,
            "Fisherman's Wharf": 5,
            "Russian Hill": 4,
            "Marina District": 9,
            "Chinatown": 6,
            "Pacific Heights": 8,
            "The Castro": 23,
            "Nob Hill": 7,
            "Sunset District": 27,
        },
        "Chinatown": {
            "Union Square": 7,
            "Mission District": 17,
            "Fisherman's Wharf": 8,
            "Russian Hill": 7,
            "Marina District": 12,
            "North Beach": 3,
            "Pacific Heights": 10,
            "The Castro": 22,
            "Nob Hill": 9,
            "Sunset District": 29,
        },
        "Pacific Heights": {
            "Union Square": 12,
            "Mission District": 15,
            "Fisherman's Wharf": 13,
            "Russian Hill": 7,
            "Marina District": 6,
            "North Beach": 9,
            "Chinatown": 11,
            "The Castro": 16,
            "Nob Hill": 8,
            "Sunset District": 21,
        },
        "The Castro": {
            "Union Square": 19,
            "Mission District": 7,
            "Fisherman's Wharf": 24,
            "Russian Hill": 18,
            "Marina District": 21,
            "North Beach": 20,
            "Chinatown": 22,
            "Pacific Heights": 16,
            "Nob Hill": 16,
            "Sunset District": 17,
        },
        "Nob Hill": {
            "Union Square": 7,
            "Mission District": 13,
            "Fisherman's Wharf": 10,
            "Russian Hill": 5,
            "Marina District": 11,
            "North Beach": 8,
            "Chinatown": 6,
            "Pacific Heights": 8,
            "The Castro": 17,
            "Sunset District": 24,
        },
        "Sunset District": {
            "Union Square": 30,
            "Mission District": 25,
            "Fisherman's Wharf": 29,
            "Russian Hill": 24,
            "Marina District": 21,
            "North Beach": 28,
            "Chinatown": 30,
            "Pacific Heights": 21,
            "The Castro": 17,
            "Nob Hill": 27,
        }
    }
    
    # Function to get travel time between two locations.
    def travel_time(from_loc, to_loc):
        return travel_times[from_loc][to_loc]

    # Decision variables:
    # For each friend i, sel[i] indicates whether we schedule a meeting with them.
    # start_vars[i] and end_vars[i] are the meeting start and end times in minutes.
    # order_vars[i] indicates the position in the itinerary (if not selected then -1).
    sel = [Bool(f"sel_{i}") for i in range(N)]
    start_vars = [Int(f"start_{i}") for i in range(N)]
    end_vars = [Int(f"end_{i}") for i in range(N)]
    order_vars = [Int(f"order_{i}") for i in range(N)]

    # Add constraints for each friend.
    for i, friend in enumerate(friends):
        # If not selected then force order to -1.
        opt.add(Or(Not(sel[i]), order_vars[i] == -1))
        # If selected then assign an order between 0 and N-1.
        opt.add(Implies(sel[i], And(order_vars[i] >= 0, order_vars[i] < N)))
        # Meeting must occur within the friend's available window and last at least the required duration.
        opt.add(Implies(sel[i],
                        And(start_vars[i] >= friend["avail_start"],
                            end_vars[i] <= friend["avail_end"],
                            end_vars[i] - start_vars[i] >= friend["min_duration"],
                            start_vars[i] < end_vars[i])))
    
    # Ensure that selected meetings get a unique order.
    for i in range(N):
        for j in range(i+1, N):
            opt.add(Implies(And(sel[i], sel[j]), order_vars[i] != order_vars[j]))
    
    # For each pair of meetings, if one is immediately after the other in the itinerary,
    # then ensure enough travel time between them.
    for i in range(N):
        for j in range(N):
            if i != j:
                opt.add(Implies(And(sel[i], sel[j], order_vars[j] == order_vars[i] + 1),
                                start_vars[j] >= end_vars[i] + travel_time(friends[i]["location"], friends[j]["location"])))
                
    # The first meeting in the itinerary must be reachable from Union Square starting at 9:00 (540).
    for i in range(N):
        opt.add(Implies(And(sel[i], order_vars[i] == 0),
                        start_vars[i] >= 540 + travel_time("Union Square", friends[i]["location"])))
    
    # For any selected meeting with order > 0, there must be a preceding meeting.
    for i in range(N):
        opt.add(Implies(And(sel[i], order_vars[i] > 0),
                        Or([And(j != i, sel[j], order_vars[j] == order_vars[i] - 1) for j in range(N)])))
    
    # Enforce that meetings are scheduled in increasing order of start time.
    for i in range(N):
        for j in range(N):
            if i != j:
                opt.add(Implies(And(sel[i], sel[j], order_vars[i] < order_vars[j]),
                                start_vars[i] < start_vars[j]))
    
    # Objective: maximize the number of scheduled meetings.
    total_meetings = Sum([If(sel[i], 1, 0) for i in range(N)])
    opt.maximize(total_meetings)

    # Solve and extract the schedule.
    if opt.check() == sat:
        m = opt.model()
        scheduled = []
        for i in range(N):
            if m.evaluate(sel[i]):
                order_val = m.evaluate(order_vars[i]).as_long()
                start_val = m.evaluate(start_vars[i]).as_long()
                end_val = m.evaluate(end_vars[i]).as_long()
                scheduled.append((order_val, i, start_val, end_val))
        # Order the meetings by their itinerary order.
        scheduled.sort(key=lambda x: x[0])
        
        def format_time(minutes):
            hrs = minutes // 60
            mins = minutes % 60
            return f"{hrs}:{mins:02d}"
        
        itinerary = []
        for order_val, i, s, e in scheduled:
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": format_time(s),
                "end_time": format_time(e)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
        
if __name__ == "__main__":
    main()