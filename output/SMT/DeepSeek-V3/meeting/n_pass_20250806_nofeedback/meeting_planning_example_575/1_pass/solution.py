from z3 import *
import json

def solve_scheduling_problem():
    # Initialize the solver
    s = Solver()

    # Define the travel times between locations (in minutes)
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

    # Define the friends and their constraints
    friends = [
        {
            'name': 'Rebecca',
            'location': 'Presidio',
            'available_start': 18 * 60 + 15,  # 6:15 PM in minutes
            'available_end': 20 * 60 + 45,    # 8:45 PM in minutes
            'duration': 60,                   # 60 minutes
        },
        {
            'name': 'Linda',
            'location': 'Sunset District',
            'available_start': 15 * 60 + 30,  # 3:30 PM in minutes
            'available_end': 19 * 60 + 45,    # 7:45 PM in minutes
            'duration': 30,                   # 30 minutes
        },
        {
            'name': 'Elizabeth',
            'location': 'Haight-Ashbury',
            'available_start': 17 * 60 + 15,  # 5:15 PM in minutes
            'available_end': 19 * 60 + 30,    # 7:30 PM in minutes
            'duration': 105,                  # 105 minutes
        },
        {
            'name': 'William',
            'location': 'Mission District',
            'available_start': 13 * 60 + 15,  # 1:15 PM in minutes
            'available_end': 19 * 60 + 30,    # 7:30 PM in minutes
            'duration': 30,                   # 30 minutes
        },
        {
            'name': 'Robert',
            'location': 'Golden Gate Park',
            'available_start': 14 * 60 + 15,  # 2:15 PM in minutes
            'available_end': 21 * 60 + 30,     # 9:30 PM in minutes
            'duration': 45,                    # 45 minutes
        },
        {
            'name': 'Mark',
            'location': 'Russian Hill',
            'available_start': 10 * 60 + 0,   # 10:00 AM in minutes
            'available_end': 21 * 60 + 15,     # 9:15 PM in minutes
            'duration': 75,                   # 75 minutes
        },
    ]

    # Current location starts at 'The Castro' at 9:00 AM (540 minutes)
    current_location = 'The Castro'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Variables to track meetings
    meetings = []
    itinerary = []

    # For each friend, create start and end time variables
    for friend in friends:
        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        s.add(start >= friend['available_start'])
        s.add(end <= friend['available_end'])
        s.add(end == start + friend['duration'])
        meetings.append({
            'name': friend['name'],
            'location': friend['location'],
            'start': start,
            'end': end,
            'duration': friend['duration'],
        })

    # Ensure no overlapping meetings and account for travel time
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            m1 = meetings[i]
            m2 = meetings[j]
            # Either m1 is before m2 or m2 is before m1
            s.add(Or(
                m1['end'] + travel_times[(m1['location'], m2['location'])] <= m2['start'],
                m2['end'] + travel_times[(m2['location'], m1['location'])] <= m1['start']
            ))

    # Ensure the first meeting is after travel from 'The Castro'
    for meeting in meetings:
        s.add(meeting['start'] >= current_time + travel_times[(current_location, meeting['location'])])

    # Try to meet as many friends as possible (optimization)
    # Here, we prioritize meeting all friends by ensuring all constraints are met
    # If not possible, we could relax constraints, but the problem seems feasible

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Collect the meetings in the itinerary
        itinerary = []
        for meeting in meetings:
            start_time = model[meeting['start']].as_long()
            end_time = model[meeting['end']].as_long()
            # Convert minutes to HH:MM format
            start_hh = start_time // 60
            start_mm = start_time % 60
            end_hh = end_time // 60
            end_mm = end_time % 60
            itinerary.append({
                'action': 'meet',
                'person': meeting['name'],
                'start_time': f"{start_hh:02d}:{start_mm:02d}",
                'end_time': f"{end_hh:02d}:{end_mm:02d}",
            })
        # Sort the itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {'itinerary': itinerary}
    else:
        return {'itinerary': []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))