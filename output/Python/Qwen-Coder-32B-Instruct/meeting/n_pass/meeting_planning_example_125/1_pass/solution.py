import json
from datetime import datetime, timedelta

# Constants
START_TIME = datetime.strptime('9:00', '%H:%M')
TRAVEL_TIMES = {
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Alamo Square'): 17,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Financial District'): 17
}
STEPHANIE_START = datetime.strptime('8:15', '%H:%M')
STEPHANIE_END = datetime.strptime('11:30', '%H:%M')
STEPHANIE_MIN_MEET = timedelta(minutes=90)
JOHN_START = datetime.strptime('10:15', '%H:%M')
JOHN_END = datetime.strptime('20:45', '%H:%M')
JOHN_MIN_MEET = timedelta(minutes=30)

def time_to_str(time):
    return time.strftime('%H:%M')

def find_meeting_schedule():
    itinerary = []
    current_location = 'Embarcadero'
    current_time = START_TIME

    # Try to meet Stephanie first if possible
    stephanie_meet_start = max(current_time + timedelta(minutes=TRAVEL_TIMES[(current_location, 'Financial District')]), STEPHANIE_START)
    stephanie_meet_end = min(stephanie_meet_start + STEPHANIE_MIN_MEET, STEPHANIE_END)

    if stephanie_meet_end - stephanie_meet_start >= STEPHANIE_MIN_MEET:
        itinerary.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Stephanie",
            "start_time": time_to_str(stephanie_meet_start),
            "end_time": time_to_str(stephanie_meet_end)
        })
        current_location = 'Financial District'
        current_time = stephanie_meet_end

    # Try to meet John next if possible
    john_meet_start = max(current_time + timedelta(minutes=TRAVEL_TIMES[(current_location, 'Alamo Square')]), JOHN_START)
    john_meet_end = min(john_meet_start + JOHN_MIN_MEET, JOHN_END)

    if john_meet_end - john_meet_start >= JOHN_MIN_MEET:
        itinerary.append({
            "action": "meet",
            "location": "Alamo Square",
            "person": "John",
            "start_time": time_to_str(john_meet_start),
            "end_time": time_to_str(john_meet_end)
        })

    return itinerary

schedule = find_meeting_schedule()
print(json.dumps({"itinerary": schedule}))