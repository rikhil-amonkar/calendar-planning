import json
from z3 import *

def main():
    # Locations: 0=Pacific Heights, 1=Golden Gate Park, 2=The Castro, 3=Bayview, 4=Marina District, 5=Union Square, 6=Sunset District, 7=Alamo Square, 8=Financial District, 9=Mission District
    travel_time = [
        [0, 15, 16, 22, 6, 12, 21, 10, 13, 15],
        [16, 0, 13, 23, 16, 22, 10, 9, 26, 17],
        [16, 11, 0, 19, 21, 19, 17, 8, 21, 7],
        [23, 22, 19, 0, 27, 18, 23, 16, 19, 13],
        [7, 18, 22, 27, 0, 16, 19, 15, 17, 20],
        [15, 22, 17, 15, 18, 0, 27, 15, 9, 14],
        [21, 11, 17, 22, 21, 30, 0, 17, 30, 25],
        [10, 9, 8, 16, 15, 14, 16, 0, 17, 10],
        [13, 23, 20, 19, 15, 9, 30, 17, 0, 17],
        [16, 17, 7, 14, 19, 15, 24, 11, 15, 0]
    ]
    
    friends = [
        {"name": "Helen", "loc": 1, "win_start": 30, "win_end": 195, "dur": 45},
        {"name": "Steven", "loc": 2, "win_start": 675, "win_end": 780, "dur": 105},
        {"name": "Deborah", "loc": 3, "win_start": -30, "win_end": 180, "dur": 30},
        {"name": "Matthew", "loc": 4, "win_start": 15, "win_end": 315, "dur": 45},
        {"name": "Joseph", "loc": 5, "win_start": 315, "win_end": 585, "dur": 120},
        {"name": "Ronald", "loc": 6, "win_start": 420, "win_end": 705, "dur": 60},
        {"name": "Robert", "loc": 7, "win_start": 570, "win_end": 735, "dur": 120},
        {"name": "Rebecca", "loc": 8, "win_start": 345, "win_end": 435, "dur": 30},
        {"name": "Elizabeth", "loc": 9, "win_start": 570, "win_end": 720, "dur": 120}
    ]
    
    n = len(friends)
    s = Solver()
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    
    # Constraints for each friend
    for i in range(n):
        # Effective start time: if window starts before 9:00, use 0 (9:00 AM)
        effective_start = max(0, friends[i]['win_start'])
        # Constraint: if meeting, start time >= max(0, friend's window start) and start time + duration <= window end
        s.add(Implies(meet[i], start_vars[i] >= effective_start))
        s.add(Implies(meet[i], start_vars[i] + friends[i]['dur'] <= friends[i]['win_end']))
        # Travel time from Pacific Heights (location 0) to friend's location
        travel_from_start = travel_time[0][friends[i]['loc']]
        s.add(Implies(meet[i], start_vars[i] >= travel_from_start))
    
    # Pairwise constraints for every pair of friends
    for i in range(n):
        for j in range(i+1, n):
            loc_i = friends[i]['loc']
            loc_j = friends[j]['loc']
            travel_ij = travel_time[loc_i][loc_j]
            travel_ji = travel_time[loc_j][loc_i]
            # If both meetings happen, one must start after the other ends plus travel time
            s.add(Implies(And(meet[i], meet[j]),
                            Or(start_vars[j] >= start_vars[i] + friends[i]['dur'] + travel_ij,
                               start_vars[i] >= start_vars[j] + friends[j]['dur'] + travel_ji)))
    
    # Maximize the number of meetings
    meet_count = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(meet_count)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(n):
            if is_true(model[meet[i]]):
                start_val = model[start_vars[i]].as_long()
                dur = friends[i]['dur']
                # Convert start time to HH:MM
                total_minutes = start_val
                hours = 9 + total_minutes // 60
                minutes = total_minutes % 60
                start_time = f"{hours:02d}:{minutes:02d}"
                # End time
                end_minutes = total_minutes + dur
                end_hours = 9 + end_minutes // 60
                end_minutes = end_minutes % 60
                end_time = f"{end_hours:02d}:{end_minutes:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i]['name'],
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()