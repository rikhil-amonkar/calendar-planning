from z3 import *

def main():
    # Build the travel time matrix (6x6) for locations 0 to 5
    travel_matrix = [
        [0, 11, 18, 12, 17, 23],
        [12, 0, 15, 16, 15, 22],
        [19, 13, 0, 23, 23, 25],
        [11, 15, 22, 0, 7, 13],
        [17, 16, 23, 7, 0, 7],
        [22, 22, 26, 12, 7, 0]
    ]
    
    # Friends data: index 0 to 4
    friends = {
        'names': ['Stephanie', 'Sandra', 'Richard', 'Brian', 'Jason'],
        'locations': [1, 2, 3, 4, 5],
        'available_start': [495, 780, 435, 735, 510],
        'available_end': [825, 1170, 615, 960, 1065],
        'duration': [90, 15, 75, 120, 60]
    }
    
    n_friends = len(friends['names'])
    
    # Create the solver for optimization
    s = Optimize()
    
    # Variables for each friend: whether we meet, start time, and position in the schedule
    meet = [Bool(f"meet_{i}") for i in range(n_friends)]
    start = [Int(f"start_{i}") for i in range(n_friends)]
    pos = [Int(f"pos_{i}") for i in range(n_friends)]
    
    # Maximize the number of meetings
    num_meetings = Sum([If(meet[i], 1, 0) for i in range(n_friends)])
    s.maximize(num_meetings)
    
    # Constraints for each friend
    for i in range(n_friends):
        s.add(If(meet[i],
                 And(
                     start[i] >= friends['available_start'][i],
                     start[i] + friends['duration'][i] <= friends['available_end'][i],
                     pos[i] >= 0,
                     pos[i] <= n_friends-1
                 ),
                 True))
    
    # Distinct positions for friends that are met
    for i in range(n_friends):
        for j in range(i+1, n_friends):
            s.add(If(And(meet[i], meet[j]),
                     pos[i] != pos[j],
                     True))
    
    # Travel constraint: from start location (0) to each friend j (if met)
    for j in range(n_friends):
        travel_time = travel_matrix[0][friends['locations'][j]]
        s.add(If(meet[j],
                 start[j] >= 540 + travel_time,
                 True))
    
    # Travel constraints between friends
    for i in range(n_friends):
        for j in range(n_friends):
            if i == j:
                continue
            travel_time = travel_matrix[friends['locations'][i]][friends['locations'][j]]
            s.add(If(And(meet[i], meet[j], pos[i] < pos[j]),
                     start[j] >= start[i] + friends['duration'][i] + travel_time,
                     True))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        num_met = m.evaluate(num_meetings)
        print(f"Number of meetings: {num_met}")
        
        schedule = []
        for i in range(n_friends):
            if m.evaluate(meet[i]):
                s_val = m.evaluate(start[i])
                p_val = m.evaluate(pos[i])
                total_minutes = s_val.as_long()
                hours = total_minutes // 60
                minutes = total_minutes % 60
                time_str = f"{hours}:{minutes:02d}"
                schedule.append((p_val.as_long(), i, total_minutes, time_str))
        
        schedule.sort(key=lambda x: x[0])
        print("Schedule (in order of visits):")
        for order, idx, start_time, time_str in schedule:
            name = friends['names'][idx]
            loc_idx = friends['locations'][idx]
            dur = friends['duration'][idx]
            end_time = start_time + dur
            end_hours = end_time // 60
            end_minutes = end_time % 60
            end_str = f"{end_hours}:{end_minutes:02d}"
            print(f"  Position {order}: Meet {name} at location {loc_idx} from {time_str} to {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()