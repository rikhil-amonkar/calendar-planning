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

    # Initial constraint: start at Richmond at 9:00 AM (time = 0)
    current_time = 0
    current_location = districts['Richmond']

    # Create decision variables for meeting order
    meeting_order = [Int(f"order_{i}") for i in range(len(friends))]
    opt.add(Distinct(meeting_order))
    for i in range(len(friends)):
        opt.add(And(meeting_order[i] >= 0, meeting_order[i] < len(friends)))

    # Add travel time constraints based on meeting order
    for i in range(len(friends)-1):
        # Get current and next meeting based on order
        current = meeting_order[i]
        next_meet = meeting_order[i+1]
        
        # Get corresponding friend info
        current_friend = friends[current]
        next_friend = friends[next_meet]
        
        # Add travel time constraint if both meetings happen
        opt.add(Implies(And(current_friend['met'], next_friend['met']),
                    next_friend['arrival'] >= current_friend['departure'] + 
                    travel_times[districts[current_friend['district']]][districts[next_friend['district']]]))

    # Ensure Kenneth is met (since his meeting is in the evening)
    opt.add(friends[-1]['met'] == True)

    # Ensure Margaret is met in the morning (since she's only available until 1:30 PM)
    opt.add(friends[3]['met'] == True)

    # Maximize the number of friends met (excluding Kenneth and Margaret who must be met)
    opt.maximize(Sum([If(f['met'], 1, 0) for f in friends if f['name'] not in ['Kenneth', 'Margaret']]))

    if opt.check() == sat:
        m = opt.model()
        schedule = []
        order = sorted([(m.evaluate(o).as_long(), f) for o, f in zip(meeting_order, friends)])
        
        for idx, friend in order:
            if m.evaluate(friend['met']):
                arr = m.evaluate(friend['arrival']).as_long() + 540
                dep = m.evaluate(friend['departure']).as_long() + 540
                arr_time = f"{arr//60}:{arr%60:02d}"
                dep_time = f"{dep//60}:{dep%60:02d}"
                schedule.append({
                    'action': 'meet',
                    'person': friend['name'],
                    'location': friend['district'],
                    'start_time': arr_time,
                    'end_time': dep_time
                })
        
        # Print the valid schedule
        print("Valid schedule found:")
        for event in schedule:
            print(f"Meet {event['person']} at {event['location']} from {event['start_time']} to {event['end_time']}")
    else:
        print("No valid schedule found that satisfies all constraints")

solve_scheduling()