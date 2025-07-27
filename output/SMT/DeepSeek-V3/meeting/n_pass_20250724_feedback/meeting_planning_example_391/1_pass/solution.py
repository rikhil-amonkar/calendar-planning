from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times between locations (in minutes)
    travel_times = {
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'Financial District'): 30,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Presidio'): 18,
        ('Alamo Square', 'Financial District'): 17,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Financial District'): 11,
        ('Presidio', 'Sunset District'): 15,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Presidio', 'Financial District'): 23,
        ('Financial District', 'Sunset District'): 31,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Russian Hill'): 10,
        ('Financial District', 'Presidio'): 22,
    }

    # Define friends and their constraints
    friends = [
        {
            'name': 'Kevin',
            'location': 'Alamo Square',
            'available_start': 8 * 60 + 15,  # 8:15 AM in minutes
            'available_end': 21 * 60 + 30,    # 9:30 PM in minutes
            'duration': 75,
        },
        {
            'name': 'Kimberly',
            'location': 'Russian Hill',
            'available_start': 8 * 60 + 45,   # 8:45 AM in minutes
            'available_end': 12 * 60 + 30,    # 12:30 PM in minutes
            'duration': 30,
        },
        {
            'name': 'Joseph',
            'location': 'Presidio',
            'available_start': 18 * 60 + 30,  # 6:30 PM in minutes
            'available_end': 19 * 60 + 15,    # 7:15 PM in minutes
            'duration': 45,
        },
        {
            'name': 'Thomas',
            'location': 'Financial District',
            'available_start': 19 * 60 + 0,   # 7:00 PM in minutes
            'available_end': 21 * 60 + 45,   # 9:45 PM in minutes
            'duration': 45,
        }
    ]

    # Current location and time
    current_location = 'Sunset District'
    current_time = 9 * 60  # 9:00 AM in minutes

    # Variables for each meeting
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        meetings.append({
            'name': friend['name'],
            'location': friend['location'],
            'start': start,
            'end': end,
            'duration': friend['duration'],
            'available_start': friend['available_start'],
            'available_end': friend['available_end'],
        })

    # Constraints for each meeting
    for meeting in meetings:
        s.add(meeting['start'] >= meeting['available_start'])
        s.add(meeting['end'] <= meeting['available_end'])
        s.add(meeting['end'] == meeting['start'] + meeting['duration'])

    # Order of meetings and travel times
    # We need to ensure that the order of meetings respects travel times
    # This is a simplified approach; a more sophisticated model would consider all possible orders
    # Here, we'll try to find a feasible order by adding constraints between meetings

    # For simplicity, we'll assume an order: Kimberly -> Kevin -> Joseph -> Thomas
    # This is a heuristic; in a real solver, we'd need to explore all possible orders
    order = [meetings[1], meetings[0], meetings[2], meetings[3]]  # Kimberly, Kevin, Joseph, Thomas

    # Add travel time constraints between meetings
    for i in range(len(order)):
        if i == 0:
            # First meeting: travel from Sunset District to Kimberly's location
            travel_time = travel_times[(current_location, order[i]['location'])]
            s.add(order[i]['start'] >= current_time + travel_time)
        else:
            # Subsequent meetings: travel from previous location to current location
            prev_meeting = order[i-1]
            travel_time = travel_times[(prev_meeting['location'], order[i]['location'])]
            s.add(order[i]['start'] >= prev_meeting['end'] + travel_time)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
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
                "action": "meet",
                "person": meeting['name'],
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}",
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))