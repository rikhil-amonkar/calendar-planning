from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the districts and their travel times
    districts = {
        'Marina District': 0,
        'Mission District': 1,
        'Fisherman\'s Wharf': 2,
        'Presidio': 3,
        'Union Square': 4,
        'Sunset District': 5,
        'Financial District': 6,
        'Haight-Ashbury': 7,
        'Russian Hill': 8
    }

    # Travel times matrix (districts x districts)
    travel_times = [
        [0, 20, 10, 10, 16, 19, 17, 16, 8],    # Marina District
        [19, 0, 22, 25, 15, 24, 15, 12, 15],    # Mission District
        [9, 22, 0, 17, 13, 27, 11, 22, 7],      # Fisherman's Wharf
        [11, 26, 19, 0, 22, 15, 23, 15, 14],    # Presidio
        [18, 14, 15, 24, 0, 27, 9, 18, 13],     # Union Square
        [21, 25, 29, 16, 30, 0, 30, 15, 24],    # Sunset District
        [15, 17, 10, 22, 9, 30, 0, 19, 11],     # Financial District
        [17, 11, 23, 15, 19, 15, 21, 0, 17],    # Haight-Ashbury
        [7, 16, 7, 14, 10, 23, 11, 17, 0]       # Russian Hill
    ]

    # Friends and their constraints
    friends = [
        {'name': 'Karen', 'district': 'Mission District', 'start': '14:15', 'end': '22:00', 'duration': 30},
        {'name': 'Richard', 'district': 'Fisherman\'s Wharf', 'start': '14:30', 'end': '17:30', 'duration': 30},
        {'name': 'Robert', 'district': 'Presidio', 'start': '21:45', 'end': '22:45', 'duration': 60},
        {'name': 'Joseph', 'district': 'Union Square', 'start': '11:45', 'end': '14:45', 'duration': 120},
        {'name': 'Helen', 'district': 'Sunset District', 'start': '14:45', 'end': '20:45', 'duration': 105},
        {'name': 'Elizabeth', 'district': 'Financial District', 'start': '10:00', 'end': '12:45', 'duration': 75},
        {'name': 'Kimberly', 'district': 'Haight-Ashbury', 'start': '14:15', 'end': '17:30', 'duration': 105},
        {'name': 'Ashley', 'district': 'Russian Hill', 'start': '11:30', 'end': '21:30', 'duration': 45}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each friend's meeting start and end times
    for friend in friends:
        friend['start_var'] = Int(f"{friend['name']}_start")
        friend['end_var'] = Int(f"{friend['name']}_end")
        s.add(friend['start_var'] >= time_to_minutes(friend['start']))
        s.add(friend['end_var'] <= time_to_minutes(friend['end']))
        s.add(friend['end_var'] - friend['start_var'] >= friend['duration'])

    # Initial position is Marina District at time 0 (9:00 AM)
    current_district = districts['Marina District']
    current_time = 0

    # Create a list to track the order of meetings
    meeting_order = []

    # We need to ensure that travel times are respected between meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # Ensure that if meeting j is after meeting i, there's enough travel time
                s.add(Or(
                    friends[j]['start_var'] >= friends[i]['end_var'] + travel_times[districts[friends[i]['district']]][districts[friends[j]['district']]],
                    friends[i]['start_var'] >= friends[j]['end_var'] + travel_times[districts[friends[j]['district']]][districts[friends[i]['district']]]
                ))

    # Ensure that the first meeting is after the initial time plus travel time
    for friend in friends:
        s.add(friend['start_var'] >= travel_times[current_district][districts[friend['district']]])

    # Try to maximize the number of friends met (all in this case)
    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            start = m[friend['start_var']].as_long()
            end = m[friend['end_var']].as_long()
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))