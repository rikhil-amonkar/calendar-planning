from z3 import *

def solve_scheduling():
    # Initialize the optimizer
    opt = Optimize()

    # Define districts and travel times
    districts = {
        'Richmond': 0,
        'Marina': 1,
        'Chinatown': 2,
        'Financial': 3,
        'Bayview': 4,
        'UnionSquare': 5
    }

    travel_times = [
        [0, 9, 20, 22, 26, 21],    # Richmond
        [11, 0, 16, 17, 27, 16],    # Marina
        [20, 12, 0, 5, 22, 7],      # Chinatown
        [21, 15, 5, 0, 19, 9],      # Financial
        [25, 25, 18, 19, 0, 17],    # Bayview
        [20, 18, 7, 9, 15, 0]       # UnionSquare
    ]

    def time_to_minutes(h, m):
        return h * 60 + m - 540  # Convert to minutes since 9:00 AM (540)

    friends = [
        {'name': 'Kimberly', 'district': 'Marina', 'start': time_to_minutes(13, 15), 
         'end': time_to_minutes(16, 45), 'duration': 15, 'met': Bool('met_Kimberly')},
        {'name': 'Robert', 'district': 'Chinatown', 'start': time_to_minutes(12, 15), 
         'end': time_to_minutes(20, 15), 'duration': 15, 'met': Bool('met_Robert')},
        {'name': 'Rebecca', 'district': 'Financial', 'start': time_to_minutes(13, 15), 
         'end': time_to_minutes(16, 45), 'duration': 75, 'met': Bool('met_Rebecca')},
        {'name': 'Margaret', 'district': 'Bayview', 'start': time_to_minutes(9, 30), 
         'end': time_to_minutes(13, 30), 'duration': 30, 'met': Bool('met_Margaret')},
        {'name': 'Kenneth', 'district': 'UnionSquare', 'start': time_to_minutes(19, 30), 
         'end': time_to_minutes(21, 15), 'duration': 75, 'met': Bool('met_Kenneth')}
    ]

    # Create variables for arrival and departure times
    for friend in friends:
        friend['arrival'] = Int(f"arrival_{friend['name']}")
        friend['departure'] = Int(f"departure_{friend['name']}")
        # Meeting must be within availability window if met
        opt.add(Implies(friend['met'], 
                    And(friend['arrival'] >= friend['start'],
                        friend['departure'] <= friend['end'],
                        friend['departure'] - friend['arrival'] >= friend['duration'])))

    # Create meeting order variables
    meeting_order = [Int(f"order_{i}") for i in range(len(friends))]
    opt.add(Distinct(meeting_order))
    for i in range(len(friends)):
        opt.add(And(meeting_order[i] >= 0, meeting_order[i] < len(friends)))

    # Add travel time constraints
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # If meeting i comes before meeting j
                before = And(meeting_order[i] < meeting_order[j], friends[i]['met'], friends[j]['met'])
                # Then j's arrival must be after i's departure plus travel time
                travel = travel_times[districts[friends[i]['district']]][districts[friends[j]['district']]]
                opt.add(Implies(before, friends[j]['arrival'] >= friends[i]['departure'] + travel))

    # Must meet Kenneth (evening meeting)
    opt.add(friends[-1]['met'] == True)
    # Must meet Margaret (morning meeting)
    opt.add(friends[3]['met'] == True)

    # Maximize number of other friends met
    other_friends = [f for f in friends if f['name'] not in ['Kenneth', 'Margaret']]
    opt.maximize(Sum([If(f['met'], 1, 0) for f in other_friends]))

    if opt.check() == sat:
        m = opt.model()
        # Get meeting order
        ordered_meetings = sorted([(m.evaluate(o).as_long(), f) for o, f in zip(meeting_order, friends)])
        
        # Build schedule
        schedule = []
        for idx, friend in ordered_meetings:
            if m.evaluate(friend['met']):
                arr = m.evaluate(friend['arrival']).as_long() + 540
                dep = m.evaluate(friend['departure']).as_long() + 540
                arr_time = f"{arr//60}:{arr%60:02d}"
                dep_time = f"{dep//60}:{dep%60:02d}"
                schedule.append({
                    'person': friend['name'],
                    'location': friend['district'],
                    'start': arr_time,
                    'end': dep_time
                })
        
        # Print schedule
        print("Valid schedule found:")
        for meeting in schedule:
            print(f"Meet {meeting['person']} at {meeting['location']} from {meeting['start']} to {meeting['end']}")
    else:
        print("No valid schedule found that satisfies all constraints")

solve_scheduling()