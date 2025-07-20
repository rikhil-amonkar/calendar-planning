from z3 import *

def main():
    meetings = [
        {"name": "Robert", "location": 3, "start_available": 465, "end_available": 630, "duration": 90},
        {"name": "Steven", "location": 4, "start_available": 510, "end_available": 1020, "duration": 75},
        {"name": "Anthony", "location": 5, "start_available": 465, "end_available": 1185, "duration": 15},
        {"name": "Sandra", "location": 6, "start_available": 885, "end_available": 1305, "duration": 45},
        {"name": "Kevin", "location": 2, "start_available": 1155, "end_available": 1305, "duration": 75},
        {"name": "Stephanie", "location": 1, "start_available": 1200, "end_available": 1245, "duration": 15}
    ]
    
    travel_matrix = [
        [0, 17, 23, 15, 7, 5, 12],
        [17, 0, 7, 5, 21, 15, 7],
        [22, 7, 0, 11, 25, 20, 12],
        [13, 5, 11, 0, 17, 11, 8],
        [7, 19, 24, 20, 0, 10, 16],
        [5, 13, 19, 11, 9, 0, 10],
        [11, 7, 13, 8, 15, 10, 0]
    ]
    
    n = len(meetings)
    s = [Int(f's_{i}') for i in range(n)]
    e = [Int(f'e_{i}') for i in range(n)]
    meet = [Bool(f'meet_{i}') for i in range(n)]
    order = [Int(f'order_{i}') for i in range(n)]
    
    opt = Optimize()
    
    # Meeting must be scheduled within availability window and have correct duration
    for i in range(n):
        opt.add(Implies(meet[i], s[i] >= meetings[i]["start_available"]))
        opt.add(Implies(meet[i], e[i] <= meetings[i]["end_available"]))
        opt.add(Implies(meet[i], e[i] == s[i] + meetings[i]["duration"]))
        opt.add(Implies(meet[i], s[i] >= 540))  # Start after 9:00 AM
    
    # Order constraints
    for i in range(n):
        # If meeting is scheduled, order is between 0 and n-1, else -1
        opt.add(If(meet[i], And(order[i] >= 0, order[i] < n), order[i] == -1))
    
    # All scheduled meetings have distinct orders
    scheduled_orders = [If(meet[i], order[i], -1) for i in range(n)]
    opt.add(Distinct(scheduled_orders))
    
    # Contiguous order sequence
    m = Sum([If(meet_i, 1, 0) for meet_i in meet])
    for i in range(n):
        opt.add(Implies(And(meet[i], order[i] > 0),
                        Or([And(meet[j], order[j] == order[i] - 1) for j in range(n) if i != j])))
    
    # Travel time constraints between consecutive meetings
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            travel_time = travel_matrix[loc_i][loc_j]
            # If j comes immediately after i
            opt.add(Implies(And(meet[i], meet[j], order[j] == order[i] + 1),
                            s[j] >= e[i] + travel_time))
    
    # First meeting must account for travel from start location (0)
    for i in range(n):
        travel_time = travel_matrix[0][meetings[i]["location"]]
        opt.add(Implies(And(meet[i], order[i] == 0),
                        s[i] >= 540 + travel_time))
    
    # Maximize number of scheduled meetings
    opt.maximize(Sum([If(meet_i, 1, 0) for meet_i in meet]))
    
    # Solve and format output
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(n):
            if is_true(model.evaluate(meet[i])):
                start_min = model.evaluate(s[i]).as_long()
                end_min = model.evaluate(e[i]).as_long()
                start_str = f"{start_min//60:02d}:{start_min%60:02d}"
                end_str = f"{end_min//60:02d}:{end_min%60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meetings[i]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by actual start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()