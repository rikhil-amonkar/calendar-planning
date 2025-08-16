import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Marina District'): 19,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Marina District'): 11,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Marina District'): 9,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Marina District'): 9,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Marina District'): 12,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Marina District'): 15,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Financial District'): 17,
}

# Define meeting constraints
meetings = {
    'Laura': {'location': 'Alamo Square', 'start': '14:30', 'end': '16:15', 'min_duration': 75},
    'Brian': {'location': 'Presidio', 'start': '10:15', 'end': '17:00', 'min_duration': 30},
    'Karen': {'location': 'Russian Hill', 'start': '18:00', 'end': '20:15', 'min_duration': 90},
    'Stephanie': {'location': 'North Beach', 'start': '10:15', 'end': '16:00', 'min_duration': 75},
    'Helen': {'location': 'Golden Gate Park', 'start': '11:30', 'end': '21:45', 'min_duration': 120},
    'Sandra': {'location': 'Richmond District', 'start': '08:00', 'end': '15:15', 'min_duration': 30},
    'Mary': {'location': 'Embarcadero', 'start': '16:45', 'end': '18:45', 'min_duration': 120},
    'Deborah': {'location': 'Financial District', 'start': '19:00', 'end': '20:45', 'min_duration': 105},
    'Elizabeth': {'location': 'Marina District', 'start': '08:30', 'end': '13:15', 'min_duration': 105},
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def time_to_str(dt):
    return dt.strftime('%H:%M')

def find_optimal_schedule():
    start_time = parse_time('9:00')
    current_location = 'Mission District'
    itinerary = []
    available_meetings = meetings.copy()

    while available_meetings:
        best_meeting = None
        best_end_time = None

        for person, details in available_meetings.items():
            location = details['location']
            start = parse_time(details['start'])
            end = parse_time(details['end'])
            min_duration = details['min_duration']

            # Calculate travel time
            travel_time = travel_times.get((current_location, location), float('inf'))
            arrival_time = start_time + timedelta(minutes=travel_time)

            # Check if we can meet within the person's availability
            if start <= arrival_time <= end - timedelta(minutes=min_duration):
                meeting_start = arrival_time
                meeting_end = min(arrival_time + timedelta(minutes=min_duration), end)
                total_time = meeting_end - start_time

                if best_meeting is None or total_time > best_end_time - start_time:
                    best_meeting = person
                    best_end_time = meeting_end

        if best_meeting:
            details = available_meetings.pop(best_meeting)
            location = details['location']
            meeting_start = best_end_time - timedelta(minutes=details['min_duration'])
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": best_meeting,
                "start_time": time_to_str(meeting_start),
                "end_time": time_to_str(best_end_time)
            })
            start_time = best_end_time
            current_location = location
        else:
            break

    return itinerary

def main():
    itinerary = find_optimal_schedule()
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()