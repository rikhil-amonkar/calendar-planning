from z3 import *

def main():
    # Define meetings: name, location, start_available (minutes), end_available (minutes), duration (minutes)
    meetings = [
        {"name": "Robert", "location": 3, "start_available": 465, "end_available": 630, "duration": 90},  # 7:45AM to 10:30AM
        {"name": "Steven", "location": 4, "start_available": 510, "end_available": 1020, "duration": 75}, # 8:30AM to 5:00PM
        {"name": "Anthony", "location": 5, "start_available": 465, "end_available": 1185, "duration": 15}, # 7:45AM to 7:45PM
        {"name": "Sandra", "location": 6, "start_available": 885, "end_available": 1305, "duration": 45},   # 2:45PM to 9:45PM
        {"name": "Kevin", "location": 2, "start_available": 1155, "end_available": 1305, "duration": 75},   # 7:15PM to 9:45PM
        {"name": "Stephanie", "location": 1, "start_available": 1200, "end_available": 1245, "duration": 15} # 8:00PM to 8:45PM
    ]
    
    # Travel matrix: 0=Haight-Ashbury, 1=Russian Hill, 2=Fisherman's Wharf, 3=Nob Hill, 4=Golden Gate Park, 5=Alamo Square, 6=Pacific Heights
    travel_matrix = [
        [0, 17, 23, 15, 7, 5, 12],
        [17, 0, 7, 5, 21, 15, 7],
        [22, 7, 0, 11, 25, 20, 12],
        [13, 5, 11, 0, 17, 11, 8],
        [7, 19, 24, 20, 0, 10, 16],
        [5, 13, 19, 11, 9, 0, 10],
        [11, 7, 13, 8, 15, 10, 0]
    ]
    
    s = [Int(f's_{i}') for i in range(6)]
    e = [Int(f'e_{i}') for i in range(6)]
    meet = [Bool(f'meet_{i}') for i in range(6)]
    
    # Before matrix for i<j
    before = {}
    for i in range(6):
        for j in range(i+1, 6):
            before[(i, j)] = Bool(f'before_{i}_{j}')
    
    opt = Optimize()
    
    # Meeting time constraints if meeting is scheduled
    for i in range(6):
        opt.add(Implies(meet[i], s[i] >= meetings[i]["start_available"]))
        opt.add(Implies(meet[i], e[i] <= meetings[i]["end_available"]))
        opt.add(Implies(meet[i], e[i] == s[i] + meetings[i]["duration"]))
    
    # Ordering and travel constraints for pairs of meetings (if both are scheduled)
    for i in range(6):
        for j in range(i+1, 6):
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            travel_ij = travel_matrix[loc_i][loc_j]
            travel_ji = travel_matrix[loc_j][loc_i]
            # If both meetings are scheduled, then enforce ordering and travel time
            constraint = Implies(
                And(meet[i], meet[j]),
                If(
                    before[(i, j)],
                    s[j] >= e[i] + travel_ij,
                    s[i] >= e[j] + travel_ji
                )
            )
            opt.add(constraint)
    
    # For each meeting, if scheduled and has no prior meeting, then include travel from start location
    for i in range(6):
        other_meetings = []
        for j in range(6):
            if j == i:
                continue
            if j < i:
                # If j is before i, then before[(j,i)] should be true (but note: we only have for i<j, so we use (j,i) for j<i)
                other_meetings.append(And(meet[j], before[(j, i)]))
            else:  # j > i
                # If before[(i,j)] is false, then j is before i
                other_meetings.append(And(meet[j], Not(before[(i, j)])))
        exists_before_i = Or(other_meetings)
        travel_from_start = travel_matrix[0][meetings[i]["location"]]
        opt.add(Implies(meet[i], If(exists_before_i, True, s[i] >= 540 + travel_from_start)))
    
    # Transitivity: for i < j < k, if i before j and j before k, then i before k
    for i in range(6):
        for j in range(i+1, 6):
            for k in range(j+1, 6):
                trans_constraint = Implies(
                    And(meet[i], meet[j], meet[k], before[(i, j)], before[(j, k)]),
                    before[(i, k)]
                )
                opt.add(trans_constraint)
    
    # Maximize the number of meetings
    opt.maximize(Sum([If(meet_i, 1, 0) for meet_i in meet]))
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(6):
            if model.evaluate(meet[i]):
                start_val = model.evaluate(s[i])
                end_val = model.evaluate(e[i])
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": meetings[i]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:])))
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()