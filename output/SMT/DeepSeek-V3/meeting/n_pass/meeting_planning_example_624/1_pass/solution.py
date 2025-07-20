from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the locations and their travel times
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
        [0, 7, 24, 13, 23, 10, 24, 19],  # Golden_Gate_Park
        [7, 0, 23, 6, 19, 5, 19, 17],     # Haight_Ashbury
        [25, 22, 0, 26, 12, 20, 6, 7],     # Fishermans_Wharf
        [11, 6, 24, 0, 20, 8, 20, 18],     # The_Castro
        [23, 19, 8, 22, 0, 17, 3, 7],     # Chinatown
        [9, 5, 19, 8, 16, 0, 15, 13],      # Alamo_Square
        [22, 18, 5, 22, 6, 16, 0, 4],      # North_Beach
        [21, 17, 7, 21, 9, 15, 5, 0]       # Russian_Hill
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

    # Convert friend times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    for friend in friends:
        friend['start_min'] = time_to_minutes(*friend['start'])
        friend['end_min'] = time_to_minutes(*friend['end'])

    # Variables for each meeting: start time and whether it's scheduled
    meeting_vars = []
    for i, friend in enumerate(friends):
        start = Int(f'start_{i}')
        scheduled = Bool(f'scheduled_{i}')
        s.add(Implies(scheduled, start >= friend['start_min']))
        s.add(Implies(scheduled, start + friend['duration'] <= friend['end_min']))
        meeting_vars.append((start, scheduled, friend))

    # Initial location is Golden Gate Park at time 0 (9:00 AM)
    current_location = 'Golden_Gate_Park'
    current_time = 0

    # Ensure meetings are scheduled in order with travel time
    for i in range(len(meeting_vars)):
        start_i, scheduled_i, friend_i = meeting_vars[i]
        loc_i = friend_i['location']
        travel_time = travel_times[locations[current_location]][locations[loc_i]]
        s.add(Implies(scheduled_i, start_i >= current_time + travel_time))
        current_time = If(scheduled_i, start_i + friend_i['duration'], current_time)
        current_location = If(scheduled_i, loc_i, current_location)

    # Maximize the number of friends met
    total_met = sum([If(scheduled, 1, 0) for (_, scheduled, _) in meeting_vars])
    s.maximize(total_met)

    # Solve the problem
    if s.check() == sat:
        model = s.model()
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
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))