from z3 import *
import json

def main():
    locations = {
        "Alamo Square": 0,
        "Russian Hill": 1,
        "Presidio": 2,
        "Chinatown": 3,
        "Sunset District": 4,
        "The Castro": 5,
        "Embarcadero": 6,
        "Golden Gate Park": 7
    }
    
    travel_times = [
        [0, 13, 18, 16, 16, 8, 17, 9],
        [15, 0, 14, 9, 23, 21, 8, 21],
        [18, 14, 0, 21, 15, 21, 20, 12],
        [17, 7, 19, 0, 29, 22, 5, 23],
        [17, 24, 16, 30, 0, 17, 31, 11],
        [8, 18, 20, 20, 17, 0, 22, 11],
        [19, 8, 20, 7, 30, 25, 0, 25],
        [10, 19, 11, 23, 10, 13, 25, 0]
    ]
    
    friends = [
        {"name": "Emily", "location": "Russian Hill", "start": 12*60+15, "end": 14*60+15, "duration": 105},
        {"name": "Mark", "location": "Presidio", "start": 14*60+45, "end": 19*60+30, "duration": 60},
        {"name": "Deborah", "location": "Chinatown", "start": 7*60+30, "end": 15*60+30, "duration": 45},
        {"name": "Margaret", "location": "Sunset District", "start": 21*60+30, "end": 22*60+30, "duration": 60},
        {"name": "George", "location": "The Castro", "start": 7*60+30, "end": 14*60+15, "duration": 60},
        {"name": "Andrew", "location": "Embarcadero", "start": 20*60+15, "end": 22*60, "duration": 75},
        {"name": "Steven", "location": "Golden Gate Park", "start": 11*60+15, "end": 21*60+15, "duration": 105}
    ]
    
    n = len(friends)
    s = Optimize()
    
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    before = [[Bool(f"before_{i}_{j}") for j in range(n)] for i in range(n)]
    
    # Meeting duration and availability constraints
    for i in range(n):
        s.add(Implies(meet[i], 
            And(
                start[i] >= friends[i]["start"],
                end[i] == start[i] + friends[i]["duration"],
                end[i] <= friends[i]["end"]
            )
        ))
    
    # Meeting order and travel constraints
    for i in range(n):
        for j in range(n):
            if i != j:
                # If both meetings occur, one must be before the other
                s.add(Implies(And(meet[i], meet[j]), Or(before[i][j], before[j][i])))
                
                # Travel time between meetings
                loc_i = locations[friends[i]["location"]]
                loc_j = locations[friends[j]["location"]]
                travel = travel_times[loc_i][loc_j]
                
                # If i before j, then end_i + travel <= start_j
                s.add(Implies(And(meet[i], meet[j], before[i][j]), end[i] + travel <= start[j]))
    
    # Constraint for first meeting: must allow travel from Alamo Square
    for i in range(n):
        no_earlier_meetings = True
        for j in range(n):
            if i != j:
                # If meeting j exists, it shouldn't be before meeting i
                no_earlier_meetings = And(no_earlier_meetings, Implies(meet[j], Not(before[j][i])))
        # If meeting i is the first, account for travel from start
        loc_i = locations[friends[i]["location"]]
        travel_time = travel_times[0][loc_i]
        s.add(Implies(And(meet[i], no_earlier_meetings), start[i] >= 9*60 + travel_time))
    
    # Optimization objectives
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
    total_start = Sum([If(meet[i], start[i], 0) for i in range(n)])
    s.maximize(total_meetings)
    s.minimize(total_start)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            if is_true(m.evaluate(meet[i])):
                start_val = m.evaluate(start[i]).as_long()
                end_val = m.evaluate(end[i]).as_long()
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                itinerary.append({
                    "action": "meet",
                    "person": friends[i]["name"],
                    "start_time": f"{start_h:02d}:{start_m:02d}",
                    "end_time": f"{end_h:02d}:{end_m:02d}"
                })
        
        # Sort by start time
        itinerary.sort(key=lambda x: x["start_time"])
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()