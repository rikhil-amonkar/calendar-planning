import json
from datetime import datetime, timedelta
import itertools

# Setup travel times
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
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Marina District'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Marina District'): 11,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Marina District'): 7,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Marina District'): 9,
    ('Golden Gate Park', 'Richmond District'): 9,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Marina District'): 9,
    ('Embarcadero', 'Financial District'): 4,
    ('Embarcadero', 'Marina District'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Russian Hill'): 8,
}

# Setup constraints
constraints = {
    'Laura': ('Alamo Square', '14:30', '16:15', 75),
    'Brian': ('Presidio', '10:15', '17:00', 30),
    'Karen': ('Russian Hill', '18:00', '20:15', 90),
    'Stephanie': ('North Beach', '10:15', '16:00', 75),
    'Helen': ('Golden Gate Park', '11:30', '21:45', 120),
    'Sandra': ('Richmond District', '08:00', '15:15', 30),
    'Mary': ('Embarcadero', '16:45', '18:45', 120),
    'Deborah': ('Financial District', '19:00', '20:45', 105),
    'Elizabeth': ('Marina District', '08:30', '13:15', 105),
}

# Convert times to datetime
def get_time_in_minutes(time_str):
    # Convert "HH:MM" string to total minutes
    hour, minute = map(int, time_str.split(':'))
    return hour * 60 + minute

# Get the travel time between two locations
def travel_time(from_location, to_location):
    return travel_times.get((from_location, to_location), 0)

# Check if a meeting can be scheduled
def can_schedule_meeting(start_time, duration, available_start, available_end):
    return start_time >= available_start and (start_time + duration) <= available_end

def schedule_meetings():
    # Starting point at Mission District
    starting_time = get_time_in_minutes("9:00")
    current_time = starting_time
    itinerary = []

    # Meeting order based on constraints, planning for maximum meet-ups
    meeting_order = ['Elizabeth', 'Sandra', 'Brian', 'Stephanie', 'Laura', 'Helen', 'Mary', 'Deborah', 'Karen']

    for person in meeting_order:
        location, start, end, duration = constraints[person]
        available_start = get_time_in_minutes(start)
        available_end = get_time_in_minutes(end)
        
        travel_to_location = travel_time("Mission District", location)
        meeting_start_time = current_time + travel_to_location
        
        if can_schedule_meeting(meeting_start_time, duration, available_start, available_end):
            meeting_end_time = meeting_start_time + duration
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": f"{meeting_start_time // 60}:{meeting_start_time % 60:02d}",
                "end_time": f"{meeting_end_time // 60}:{meeting_end_time % 60:02d}"
            })
            current_time = meeting_end_time + travel_time(location, "Mission District")  # Travel back to Mission District
        else:
            print(f"Cannot schedule meeting with {person}.")
    
    return itinerary

def main():
    itinerary = schedule_meetings()
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()