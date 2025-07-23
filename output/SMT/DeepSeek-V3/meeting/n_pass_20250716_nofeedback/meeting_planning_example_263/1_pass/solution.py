from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Bayview': {
            'Embarcadero': 19,
            'Fisherman\'s Wharf': 25,
            'Financial District': 19
        },
        'Embarcadero': {
            'Bayview': 21,
            'Fisherman\'s Wharf': 6,
            'Financial District': 5
        },
        'Fisherman\'s Wharf': {
            'Bayview': 26,
            'Embarcadero': 8,
            'Financial District': 11
        },
        'Financial District': {
            'Bayview': 19,
            'Embarcadero': 4,  # Note: Typo in original data (Embarcadero)
            'Fisherman\'s Wharf': 10
        }
    }
    # Correcting the typo in travel_times
    travel_times['Financial District']['Embarcadero'] = 4

    # Friends' availability and meeting constraints
    friends = {
        'Betty': {
            'location': 'Embarcadero',
            'available_start': (19, 45),  # 7:45 PM
            'available_end': (21, 45),    # 9:45 PM
            'min_duration': 15            # minutes
        },
        'Karen': {
            'location': 'Fisherman\'s Wharf',
            'available_start': (8, 45),    # 8:45 AM
            'available_end': (15, 0),     # 3:00 PM
            'min_duration': 30
        },
        'Anthony': {
            'location': 'Financial District',
            'available_start': (9, 15),    # 9:15 AM
            'available_end': (21, 30),     # 9:30 PM
            'min_duration': 105
        }
    }

    # Current location starts at Bayview at 9:00 AM
    current_time_hour = 9
    current_time_minute = 0
    current_location = 'Bayview'

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(hour, minute):
        return hour * 60 + minute

    start_time = time_to_minutes(current_time_hour, current_time_minute)

    # Variables for each meeting's start and end times (in minutes since midnight)
    betty_start = Int('betty_start')
    betty_end = Int('betty_end')
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')
    anthony_start = Int('anthony_start')
    anthony_end = Int('anthony_end')

    # Convert friends' available times to minutes
    betty_available_start = time_to_minutes(19, 45)
    betty_available_end = time_to_minutes(21, 45)
    karen_available_start = time_to_minutes(8, 45)
    karen_available_end = time_to_minutes(15, 0)
    anthony_available_start = time_to_minutes(9, 15)
    anthony_available_end = time_to_minutes(21, 30)

    # Constraints for each meeting
    # Betty
    s.add(betty_start >= betty_available_start)
    s.add(betty_end <= betty_available_end)
    s.add(betty_end == betty_start + friends['Betty']['min_duration'])

    # Karen
    s.add(karen_start >= karen_available_start)
    s.add(karen_end <= karen_available_end)
    s.add(karen_end == karen_start + friends['Karen']['min_duration'])

    # Anthony
    s.add(anthony_start >= anthony_available_start)
    s.add(anthony_end <= anthony_available_end)
    s.add(anthony_end == anthony_start + friends['Anthony']['min_duration'])

    # Define the order of meetings and travel times
    # We need to decide the sequence of meetings. Let's assume the order is Karen -> Anthony -> Betty.
    # This is a plausible order given their time windows.

    # Start from Bayview at 9:00 AM (540 minutes)
    # First, travel to Karen's location (Fisherman's Wharf)
    travel_to_karen = travel_times[current_location]['Fisherman\'s Wharf']
    s.add(karen_start >= start_time + travel_to_karen)

    # After meeting Karen, travel to Anthony's location (Financial District)
    travel_to_anthony = travel_times['Fisherman\'s Wharf']['Financial District']
    s.add(anthony_start >= karen_end + travel_to_anthony)

    # After meeting Anthony, travel to Betty's location (Embarcadero)
    travel_to_betty = travel_times['Financial District']['Embarcadero']
    s.add(betty_start >= anthony_end + travel_to_betty)

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            hour = (minutes // 60) % 24
            minute = minutes % 60
            return f"{hour:02d}:{minute:02d}"

        betty_s = m[betty_start].as_long()
        betty_e = m[betty_end].as_long()
        karen_s = m[karen_start].as_long()
        karen_e = m[karen_end].as_long()
        anthony_s = m[anthony_start].as_long()
        anthony_e = m[anthony_end].as_long()

        itinerary = [
            {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_s), "end_time": minutes_to_time(karen_e)},
            {"action": "meet", "person": "Anthony", "start_time": minutes_to_time(anthony_s), "end_time": minutes_to_time(anthony_e)},
            {"action": "meet", "person": "Betty", "start_time": minutes_to_time(betty_s), "end_time": minutes_to_time(betty_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

result = solve_scheduling()
print(json.dumps(result, indent=2))