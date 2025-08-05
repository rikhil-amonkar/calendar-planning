from z3 import *

def main():
    # Travel times between districts: [Richmond, Sunset, Haight-Ashbury, Mission, Golden Gate Park]
    travel_matrix = [
        [0, 11, 10, 20, 9],    # from Richmond
        [12, 0, 15, 24, 11],    # from Sunset
        [10, 15, 0, 11, 7],     # from Haight-Ashbury
        [20, 24, 12, 0, 17],    # from Mission
        [7, 10, 7, 17, 0]       # from Golden Gate Park
    ]
    
    # Friend details: [Sarah, Richard, Elizabeth, Michelle]
    friend_names = ['Sarah', 'Richard', 'Elizabeth', 'Michelle']
    # Availability start times in minutes from midnight (9:00 AM is 540 minutes)
    avail_start = [10*60 + 45, 11*60 + 45, 11*60 + 0, 18*60 + 15]  # 10:45, 11:45, 11:00, 18:15
    avail_end = [19*60 + 0, 15*60 + 45, 17*60 + 15, 20*60 + 45]    # 19:00, 15:45, 17:15, 20:45
    durations = [30, 90, 120, 90]  # in minutes
    # Each friend's district: 1=Sunset, 2=Haight-Ashbury, 3=Mission, 4=Golden Gate Park
    districts = [1, 2, 3, 4]  # Sarah in Sunset (1), Richard in Haight-Ashbury (2), etc.
    
    # Initialize Z3 variables
    met = [Bool(f'met_{i}') for i in range(4)]
    start_times = [Int(f'start_{i}') for i in range(4)]
    positions = [Int(f'pos_{i}') for i in range(4)]
    
    # Create an optimizer
    opt = Optimize()
    
    # Constraints for each friend
    for i in range(4):
        # If meeting is scheduled, start time must be within availability
        opt.add(Implies(met[i], start_times[i] >= avail_start[i]))
        opt.add(Implies(met[i], start_times[i] + durations[i] <= avail_end[i]))
        # Start time must include travel from Richmond (district 0)
        opt.add(Implies(met[i], start_times[i] >= 540 + travel_matrix[0][districts[i]]))
        # Position must be between 0 and 3 if meeting is scheduled
        opt.add(Implies(met[i], And(positions[i] >= 0, positions[i] < 4)))
    
    # Ensure distinct positions for scheduled meetings
    for i in range(4):
        for j in range(i + 1, 4):
            opt.add(Implies(And(met[i], met[j]), positions[i] != positions[j]))
    
    # Travel time constraints between consecutive meetings
    for i in range(4):
        for j in range(4):
            if i != j:
                # If both meetings are scheduled and i comes before j, ensure travel time is accounted for
                condition = And(met[i], met[j], positions[i] < positions[j])
                travel_time = travel_matrix[districts[i]][districts[j]]
                opt.add(Implies(condition, start_times[j] >= start_times[i] + durations[i] + travel_time))
    
    # Maximize the number of meetings scheduled
    total_met = Sum([If(met[i], 1, 0) for i in range(4)])
    opt.maximize(total_met)
    
    # Solve the problem
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(4):
            if model.eval(met[i]):
                start_val = model.eval(start_times[i]).as_long()
                end_val = start_val + durations[i]
                # Format times as HH:MM
                start_str = f"{start_val // 60:02d}:{start_val % 60:02d}"
                end_str = f"{end_val // 60:02d}:{end_val % 60:02d}"
                itinerary.append({
                    'action': 'meet',
                    'person': friend_names[i],
                    'start_time': start_str,
                    'end_time': end_str
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        result = {'itinerary': itinerary}
        print(f"SOLUTION: {result}")
    else:
        print('SOLUTION: {"itinerary": []}')

if __name__ == '__main__':
    main()