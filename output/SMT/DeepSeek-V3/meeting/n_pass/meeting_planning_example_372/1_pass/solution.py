from z3 import *

def solve_scheduling():
    s = Solver()

    # Travel times (in minutes)
    travel = {
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Mission District'): 24,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Mission District'): 10,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Mission District'): 16,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
    }

    # Friends' availability
    friends = {
        'Charles': {'location': 'Alamo Square', 'start': 18*60, 'end': 20*60 + 45, 'duration': 90},
        'Margaret': {'location': 'Russian Hill', 'start': 9*60, 'end': 16*60, 'duration': 30},
        'Daniel': {'location': 'Golden Gate Park', 'start': 8*60, 'end': 13*60 + 30, 'duration': 15},
        'Stephanie': {'location': 'Mission District', 'start': 20*60 + 30, 'end': 22*60, 'duration': 90},
    }

    # Current location and time
    current_location = 'Sunset District'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Create variables for each meeting
    meetings = {}
    for name in friends:
        meetings[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'location': friends[name]['location'],
        }
        s.add(meetings[name]['start'] >= friends[name]['start'])
        s.add(meetings[name]['end'] <= friends[name]['end'])
        s.add(meetings[name]['end'] == meetings[name]['start'] + friends[name]['duration'])

    # Define the order of meetings (we'll use a list to represent the sequence)
    # We need to ensure that travel times are respected between consecutive meetings
    # This is a complex constraint; for simplicity, we'll assume a fixed order
    # Here, we'll try meeting Margaret, Daniel, Charles, then Stephanie

    # Start at Sunset District at 9:00 AM
    prev_end = current_time
    prev_loc = current_location

    # Meet Margaret first
    s.add(meetings['Margaret']['start'] >= prev_end + travel[(prev_loc, meetings['Margaret']['location'])])
    prev_end = meetings['Margaret']['end']
    prev_loc = meetings['Margaret']['location']

    # Meet Daniel next
    s.add(meetings['Daniel']['start'] >= prev_end + travel[(prev_loc, meetings['Daniel']['location'])])
    prev_end = meetings['Daniel']['end']
    prev_loc = meetings['Daniel']['location']

    # Meet Charles next
    s.add(meetings['Charles']['start'] >= prev_end + travel[(prev_loc, meetings['Charles']['location'])])
    prev_end = meetings['Charles']['end']
    prev_loc = meetings['Charles']['location']

    # Meet Stephanie last
    s.add(meetings['Stephanie']['start'] >= prev_end + travel[(prev_loc, meetings['Stephanie']['location'])])

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Collect all meetings
        for name in meetings:
            start = model[meetings[name]['start']].as_long()
            end = model[meetings[name]['end']].as_long()
            start_time = f"{start // 60:02d}:{start % 60:02d}"
            end_time = f"{end // 60:02d}:{end % 60:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time,
                "end_time": end_time
            })

        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

result = solve_scheduling()
print(result)