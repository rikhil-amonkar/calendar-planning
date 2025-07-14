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

    # Create an ordered list of possible meetings
    meeting_order = []
    for friend in friends:
        meeting_order.append((friend['name'], friend['district'], 
                            friend['arrival'], friend['departure'], friend['met']))

    # Add travel time constraints between consecutive meetings
    for i in range(len(meeting_order)-1):
        name1, district1, arrival1, departure1, met1 = meeting_order[i]
        name2, district2, arrival2, _, met2 = meeting_order[i+1]
        travel_time = travel_times[districts[district1]][districts[district2]]
        opt.add(Implies(And(met1, met2), arrival2 >= departure1 + travel_time))

    # Ensure Kenneth is met (since his meeting is in the evening)
    opt.add(friends[-1]['met'] == True)

    # Maximize the number of friends met (excluding Kenneth who must be met)
    opt.maximize(Sum([If(f['met'], 1, 0) for f in friends[:-1]]))

    if opt.check() == sat:
        m = opt.model()
        schedule = []
        for friend in friends:
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
        for event in sorted(schedule, key=lambda x: x['start_time']):
            print(f"Meet {event['person']} at {event['location']} from {event['start_time']} to {event['end_time']}")
    else:
        print("No valid schedule found that satisfies all constraints")

solve_scheduling()