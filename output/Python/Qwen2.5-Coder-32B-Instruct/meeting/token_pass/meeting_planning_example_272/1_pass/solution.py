import json
from datetime import datetime, timedelta

# Constants for time conversion
START_TIME = 9 * 60  # 9:00 AM in minutes since midnight
END_TIME = 21 * 60   # 9:00 PM in minutes since midnight

# Travel times in minutes
travel_times = {
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Embarcadero'): 20,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Mission District'): 20
}

# Availability in minutes since midnight
availability = {
    'Patricia': {'location': 'Nob Hill', 'start': 1830, 'end': 2145, 'min_duration': 90},
    'Ashley': {'location': 'Mission District', 'start': 2010, 'end': 2115, 'min_duration': 45},
    'Timothy': {'location': 'Embarcadero', 'start': 585, 'end': 327, 'min_duration': 120}
}

def convert_to_minutes(time_str):
    """Convert time in 'H:MM' format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def convert_to_time(minutes):
    """Convert minutes since midnight to 'H:MM' format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def find_meeting_schedule():
    current_location = 'Russian Hill'
    current_time = START_TIME
    itinerary = []

    for person, details in availability.items():
        person_start = details['start']
        person_end = details['end']
        min_duration = details['min_duration']
        person_location = details['location']

        # Find the first feasible meeting time
        while current_time < END_TIME:
            travel_time = travel_times.get((current_location, person_location), float('inf'))
            if current_time + travel_time + min_duration <= person_end:
                meeting_start = max(current_time + travel_time, person_start)
                meeting_end = meeting_start + min_duration
                if meeting_end <= person_end:
                    itinerary.append({
                        "action": "meet",
                        "location": person_location,
                        "person": person,
                        "start_time": convert_to_time(meeting_start),
                        "end_time": convert_to_time(meeting_end)
                    })
                    current_time = meeting_end
                    current_location = person_location
                    break
            current_time += 1  # Increment time to find next feasible slot

    return itinerary

def main():
    itinerary = find_meeting_schedule()
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()