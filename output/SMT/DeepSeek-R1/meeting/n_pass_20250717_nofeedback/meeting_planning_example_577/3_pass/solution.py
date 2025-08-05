from z3 import *

def main():
    # Meeting details: name, location, availability (minutes), duration (minutes)
    meetings = [
        {"name": "Robert", "location": 3, "start_available": 465, "end_available": 630, "duration": 90},  # 7:45AM-10:30AM
        {"name": "Steven", "location": 4, "start_available": 510, "end_available": 1020, "duration": 75},  # 8:30AM-5:00PM
        {"name": "Anthony", "location": 5, "start_available": 465, "end_available": 1185, "duration": 15},  # 7:45AM-7:45PM
        {"name": "Sandra", "location": 6, "start_available": 885, "end_available": 1305, "duration": 45},  # 2:45PM-9:45PM
        {"name": "Kevin", "location": 2, "start_available": 1155, "end_available": 1305, "duration": 75},  # 7:15PM-9:45PM
        {"name": "Stephanie", "location": 1, "start_available": 1200, "end_available": 1245, "duration": 15}  # 8:00PM-8:45PM
    ]
    
    # Travel matrix: 0=Haight-Ashbury, 1=Russian Hill, 2=Fisherman's Wharf, 
    # 3=Nob Hill, 4=Golden Gate Park, 5=Alamo Square, 6=Pacific Heights
    travel_matrix = [
        [0, 17, 23, 15, 7, 5, 12],
        [17, 0, 7, 5, 21, 15, 7],
        [22, 7, 0, 11, 25, 20, 12],
        [13, 5, 11, 0, 17, 11, 8],
        [7, 19, 24, 20, 0, 10, 16],
        [5, 13, 19, 11, 9, 0, 10],
        [11, 7, 13, 8, 15, 10, 0]
    ]
    
    # Create Z3 variables
    s = [Int(f's_{i}') for i in range(6)]  # Start times
    e = [Int(f'e_{i}') for i in range(6)]  # End times
    meet = [Bool(f'meet_{i}') for i in range(6)]  # Whether meeting is scheduled
    
    # Ordering variables for meeting pairs
    before = [[Bool(f'before_{i}_{j}') for j in range(6)] for i in range(6)]
    
    opt = Optimize()
    
    # Meeting time constraints if scheduled
    for i in range(6):
        opt.add(Implies(meet[i], s[i] >= meetings[i]["start_available"]))
        opt.add(Implies(meet[i], e[i] <= meetings[i]["end_available"]))
        opt.add(Implies(meet[i], e[i] == s[i] + meetings[i]["duration"]))
    
    # Ordering and travel constraints
    for i in range(6):
        for j in range(6):
            if i == j:
                continue
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            travel_time = travel_matrix[loc_i][loc_j]
            # If both meetings are scheduled, enforce ordering and travel time
            opt.add(Implies(And(meet[i], meet[j]),
                           If(before[i][j],
                              s[j] >= e[i] + travel_time,
                              s[i] >= e[j] + travel_time)))
    
    # Exactly one direction for each pair
    for i in range(6):
        for j in range(i+1, 6):
            opt.add(Implies(And(meet[i], meet[j]), 
                           Or(before[i][j], before[j][i])))
            opt.add(Implies(And(meet[i], meet[j]), 
                           Not(And(before[i][j], before[j][i]))))
    
    # Transitivity constraints
    for i in range(6):
        for j in range(6):
            for k in range(6):
                if i == j or j == k or i == k:
                    continue
                opt.add(Implies(And(meet[i], meet[j], meet[k], before[i][j], before[j][k]),
                               before[i][k]))
    
    # First meeting must account for travel from start (9:00 AM = 540 minutes)
    for i in range(6):
        other_meetings_before = []
        for j in range(6):
            if i != j:
                other_meetings_before.append(And(meet[j], before[j][i]))
        opt.add(Implies(meet[i],
                       If(Or(other_meetings_before),
                          True,
                          s[i] >= 540 + travel_matrix[0][meetings[i]["location"]])))
    
    # Maximize number of meetings
    opt.maximize(Sum([If(meet_i, 1, 0) for meet_i in meet]))
    
    # Solve and output
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(6):
            if is_true(model.evaluate(meet[i])):
                start_min = model.evaluate(s[i]).as_long()
                end_min = model.evaluate(e[i]).as_long()
                # Convert minutes to HH:MM format
                start_str = f"{start_min//60:02d}:{start_min%60:02d}"
                end_str = f"{end_min//60:02d}:{end_min%60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meetings[i]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()