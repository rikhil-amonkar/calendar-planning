from z3 import *

def main():
    # Travel time matrix: 7x7, indexed by [from][to]
    # Locations: 0=The Castro, 1=Presidio, 2=Sunset District, 3=Haight-Ashbury, 4=Mission District, 5=Golden Gate Park, 6=Russian Hill
    travel_matrix = [
        [0, 20, 17, 6, 7, 11, 18],
        [21, 0, 15, 15, 26, 12, 14],
        [17, 16, 0, 15, 24, 11, 24],
        [6, 15, 15, 0, 11, 7, 17],
        [7, 25, 24, 12, 0, 17, 15],
        [13, 11, 10, 7, 17, 0, 19],
        [21, 14, 23, 17, 16, 21, 0]
    ]
    
    # Friends data: (name, location, min_duration, available_start, available_end)
    friends = [
        ("Rebecca", 1, 60, 555, 645),   # available_end for start: 705 - 60 = 645
        ("Linda", 2, 30, 390, 615),      # 645 - 30 = 615
        ("Elizabeth", 3, 105, 495, 525), # 630 - 105 = 525
        ("William", 4, 30, 255, 600),    # 630 - 30 = 600
        ("Robert", 5, 45, 315, 705),     # 750 - 45 = 705
        ("Mark", 6, 75, 60, 660)         # 735 - 75 = 660
    ]
    
    n_friends = len(friends)
    
    # Meeting for the starting point: The Castro at time 0
    meetings = [
        {'name': 'Start', 'loc': 0, 'start': 0, 'end': 0, 'meet': True}
    ]
    
    # Create variables for friends
    meet_vars = [Bool(f"meet_{i}") for i in range(n_friends)]
    start_vars = [Real(f"start_{i}") for i in range(n_friends)]
    
    # Add friend meetings to the meetings list
    for i in range(n_friends):
        name, loc, dur, avail_start, avail_end = friends[i]
        meetings.append({
            'name': name,
            'loc': loc,
            'start': start_vars[i],
            'end': start_vars[i] + dur,
            'meet': meet_vars[i]
        })
    
    n_meetings = len(meetings)
    s = Solver()
    
    # Time window constraints for each friend meeting
    for i in range(1, n_meetings):
        m = meetings[i]
        s.add(Implies(m['meet'], And(m['start'] >= friends[i-1][3], m['start'] <= friends[i-1][4])))
    
    # Disjunctive constraints for every pair of meetings
    for i in range(n_meetings):
        for j in range(i+1, n_meetings):
            m1 = meetings[i]
            m2 = meetings[j]
            loc_i = m1['loc']
            loc_j = m2['loc']
            travel_ij = travel_matrix[loc_i][loc_j]
            travel_ji = travel_matrix[loc_j][loc_i]
            
            # If both meetings happen, ensure they don't overlap considering travel
            disj = Or(
                m2['start'] >= m1['end'] + travel_ij,
                m1['start'] >= m2['end'] + travel_ji
            )
            s.add(Or(Not(m1['meet']), Not(m2['meet']), disj))
    
    # Objective: maximize the number of meetings
    obj = Sum([If(meet_vars[i], 1, 0) for i in range(n_friends)])
    s.maximize(obj)
    
    # Solve and output results
    if s.check() == sat:
        model = s.model()
        total_met = model.eval(obj)
        print(f"Total friends met: {total_met}")
        
        # Collect and sort scheduled meetings by start time
        schedule = []
        for i in range(1, n_meetings):
            if model.eval(meet_vars[i-1]):
                start_val = model.eval(meetings[i]['start'])
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                else:
                    start_min = int(str(start_val))
                end_min = start_min + friends[i-1][2]
                schedule.append((start_min, end_min, meetings[i]['name'], meetings[i]['loc']))
        
        # Convert minutes to time string
        def min_to_time(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        
        schedule.sort(key=lambda x: x[0])
        print("\nSchedule:")
        for start, end, name, loc in schedule:
            start_time = min_to_time(start)
            end_time = min_to_time(end)
            print(f"Meet {name} at location {loc} from {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()