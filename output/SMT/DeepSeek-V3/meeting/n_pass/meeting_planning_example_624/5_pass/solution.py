from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the optimizer
    opt = Optimize()

    # Define locations and their indices
    locations = {
        'Golden_Gate_Park': 0,
        'Haight_Ashbury': 1,
        'Fishermans_Wharf': 2,
        'The_Castro': 3,
        'Chinatown': 4,
        'Alamo_Square': 5,
        'North_Beach': 6,
        'Russian_Hill': 7
    }

    # Travel times matrix (minutes)
    travel_times = [
        [0, 7, 24, 13, 23, 10, 24, 19],
        [7, 0, 23, 6, 19, 5, 19, 17],
        [25, 22, 0, 26, 12, 20, 6, 7],
        [11, 6, 24, 0, 20, 8, 20, 18],
        [23, 19, 8, 22, 0, 17, 3, 7],
        [9, 5, 19, 8, 16, 0, 15, 13],
        [22, 18, 5, 22, 6, 16, 0, 4],
        [21, 17, 7, 21, 9, 15, 5, 0]
    ]

    # Friends' information
    friends = [
        {'name': 'Carol', 'location': 'Haight_Ashbury', 'start': (21, 30), 'end': (22, 30), 'duration': 60},
        {'name': 'Laura', 'location': 'Fishermans_Wharf', 'start': (11, 45), 'end': (21, 30), 'duration': 60},
        {'name': 'Karen', 'location': 'The_Castro', 'start': (7, 15), 'end': (14, 0), 'duration': 75},
        {'name': 'Elizabeth', 'location': 'Chinatown', 'start': (12, 15), 'end': (21, 30), 'duration': 75},
        {'name': 'Deborah', 'location': 'Alamo_Square', 'start': (12, 0), 'end': (15, 0), 'duration': 105},
        {'name': 'Jason', 'location': 'North_Beach', 'start': (14, 45), 'end': (19, 0), 'duration': 90},
        {'name': 'Steven', 'location': 'Russian_Hill', 'start': (14, 45), 'end': (18, 30), 'duration': 120}
    ]

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540

    for friend in friends:
        friend['start_min'] = time_to_minutes(*friend['start'])
        friend['end_min'] = time_to_minutes(*friend['end'])

    # Create variables for each meeting
    meeting_vars = []
    for i, friend in enumerate(friends):
        start = Int(f'start_{i}')
        scheduled = Bool(f'scheduled_{i}')
        opt.add(Implies(scheduled, start >= friend['start_min']))
        opt.add(Implies(scheduled, start + friend['duration'] <= friend['end_min']))
        meeting_vars.append((start, scheduled, friend))

    # Variables to track location and time after each meeting
    loc_vars = [Int(f'loc_{i}') for i in range(len(friends)+1)]
    time_vars = [Int(f'time_{i}') for i in range(len(friends)+1)]
    
    # Initial conditions
    opt.add(loc_vars[0] == locations['Golden_Gate_Park'])
    opt.add(time_vars[0] == 0)

    # Constraints for each meeting
    for i in range(len(friends)):
        start_i, scheduled_i, friend_i = meeting_vars[i]
        loc_i = locations[friend_i['location']]
        travel_time = Int(f'travel_{i}')
        
        # Set travel time based on previous location
        for loc_from in range(len(locations)):
            opt.add(Implies(And(scheduled_i, loc_vars[i] == loc_from),
                         travel_time == travel_times[loc_from][loc_i]))
        
        # If meeting is scheduled
        opt.add(Implies(scheduled_i,
                       And(start_i >= time_vars[i] + travel_time,
                           loc_vars[i+1] == loc_i,
                           time_vars[i+1] == start_i + friend_i['duration'])))
        
        # If meeting is not scheduled
        opt.add(Implies(Not(scheduled_i),
                       And(loc_vars[i+1] == loc_vars[i],
                           time_vars[i+1] == time_vars[i])))

    # Maximize number of meetings
    total_met = Sum([If(scheduled, 1, 0) for (_, scheduled, _) in meeting_vars])
    opt.maximize(total_met)

    # Solve
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i, (start, scheduled, friend) in enumerate(meeting_vars):
            if model.evaluate(scheduled):
                start_val = model.evaluate(start).as_long()
                h = (start_val + 540) // 60
                m = (start_val + 540) % 60
                start_time = f"{h:02d}:{m:02d}"
                end_time_val = start_val + friend['duration']
                h_end = (end_time_val + 540) // 60
                m_end = (end_time_val + 540) % 60
                end_time = f"{h_end:02d}:{m_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend['name'],
                    "start_time": start_time,
                    "end_time": end_time
                })
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling_problem()
print(json.dumps(result, indent=2))