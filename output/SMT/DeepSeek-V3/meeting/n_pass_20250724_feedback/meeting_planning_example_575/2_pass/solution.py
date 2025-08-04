from z3 import *
import json
from datetime import datetime, timedelta

def solve_scheduling():
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m - 540  # Subtract 540 to get minutes since 9:00 AM

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total = minutes + 540
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Travel times in minutes (already in minutes)
    travel_times = {
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Sunset District'): 17,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Russian Hill'): 18,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Russian Hill'): 14,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Russian Hill'): 24,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Presidio'): 25,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Russian Hill'): 15,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Golden Gate Park'): 21,
    }

    # People data with availability converted to minutes since 9:00 AM
    people = [
        {
            'name': 'Rebecca',
            'location': 'Presidio',
            'available_start': time_to_minutes("18:15"),  # 6:15 PM
            'available_end': time_to_minutes("20:45"),    # 8:45 PM
            'duration': 60
        },
        {
            'name': 'Linda',
            'location': 'Sunset District',
            'available_start': time_to_minutes("15:30"),  # 3:30 PM
            'available_end': time_to_minutes("19:45"),    # 7:45 PM
            'duration': 30
        },
        {
            'name': 'Elizabeth',
            'location': 'Haight-Ashbury',
            'available_start': time_to_minutes("17:15"),  # 5:15 PM
            'available_end': time_to_minutes("19:30"),    # 7:30 PM
            'duration': 105
        },
        {
            'name': 'William',
            'location': 'Mission District',
            'available_start': time_to_minutes("13:15"),  # 1:15 PM
            'available_end': time_to_minutes("19:30"),    # 7:30 PM
            'duration': 30
        },
        {
            'name': 'Robert',
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes("14:15"),  # 2:15 PM
            'available_end': time_to_minutes("21:30"),    # 9:30 PM
            'duration': 45
        },
        {
            'name': 'Mark',
            'location': 'Russian Hill',
            'available_start': time_to_minutes("10:00"),  # 10:00 AM
            'available_end': time_to_minutes("21:15"),    # 9:15 PM
            'duration': 75
        }
    ]

    # Create variables for each person's start time (in minutes since 9:00 AM)
    for person in people:
        person['start'] = Int(f"start_{person['name']}")
        s.add(person['start'] >= person['available_start'])
        s.add(person['start'] + person['duration'] <= person['available_end'])

    # Current location starts at The Castro at time 0 (9:00 AM)
    current_location = 'The Castro'
    current_time = 0

    # Create a list to track meeting order
    meeting_order = [p['name'] for p in people]
    order_vars = {name: Int(f"order_{name}") for name in meeting_order}
    for name in meeting_order:
        s.add(And(order_vars[name] >= 0, order_vars[name] < len(people)))

    # All order variables must be distinct
    s.add(Distinct([order_vars[name] for name in meeting_order]))

    # Add travel time constraints
    for i in range(len(people)):
        for j in range(len(people)):
            if i != j:
                # If meeting i comes before meeting j
                i_before_j = (order_vars[people[i]['name']] < order_vars[people[j]['name']])
                travel_time = travel_times[(people[i]['location'], people[j]['location'])]
                s.add(Implies(i_before_j,
                              people[i]['start'] + people[i]['duration'] + travel_time <= people[j]['start']))

    # First meeting must be reachable from starting location
    for person in people:
        travel_time = travel_times[(current_location, person['location'])]
        s.add(Implies(order_vars[person['name']] == 0,
                      person['start'] >= travel_time))

    # Optimize to meet as many friends as possible (though we want all in this case)
    # Just check satisfiability since we want to meet all friends
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for person in people:
            start = model[person['start']].as_long()
            end = start + person['duration']
            itinerary.append({
                "action": "meet",
                "person": person['name'],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        # Sort by start time
        itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))