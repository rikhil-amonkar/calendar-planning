import json
from datetime import datetime, timedelta

# Define constants
START_TIME = datetime.strptime('9:00', '%H:%M')
END_TIME = datetime.strptime('20:45', '%H:%M')  # 8:45 PM

# Travel times in minutes
travel_times = {
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Alamo Square'): 17,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Financial District'): 17
}

# Friends' availability
stephanie_start = datetime.strptime('8:15', '%H:%M')
stephanie_end = datetime.strptime('11:30', '%H:%M')
john_start = datetime.strptime('10:15', '%H:%M')
john_end = datetime.strptime('20:45', '%H:%M')

# Minimum meeting times
stephanie_min_meeting = timedelta(minutes=90)
john_min_meeting = timedelta(minutes=30)

def find_meeting_time(start, end, min_duration):
    current_time = start
    while current_time + min_duration <= end:
        yield current_time, current_time + min_duration
        current_time += timedelta(minutes=1)

def format_time(time):
    return time.strftime('%H:%M').lstrip('0') if time.hour != 0 else time.strftime('%H:%M')

def main():
    itinerary = []
    
    # Try to meet Stephanie first
    for stephanie_start_time, stephanie_end_time in find_meeting_time(stephanie_start, stephanie_end, stephanie_min_meeting):
        if START_TIME + timedelta(minutes=travel_times[('Embarcadero', 'Financial District')]) <= stephanie_start_time:
            # We can reach Financial District in time to meet Stephanie
            meeting_with_stephanie = {
                "action": "meet",
                "location": "Financial District",
                "person": "Stephanie",
                "start_time": format_time(stephanie_start_time),
                "end_time": format_time(stephanie_end_time)
            }
            itinerary.append(meeting_with_stephanie)
            
            # Calculate next possible time to meet John after meeting Stephanie
            post_stephanie_time = stephanie_end_time + timedelta(minutes=travel_times[('Financial District', 'Alamo Square')])
            for john_start_time, john_end_time in find_meeting_time(john_start, john_end, john_min_meeting):
                if post_stephanie_time <= john_start_time:
                    meeting_with_john = {
                        "action": "meet",
                        "location": "Alamo Square",
                        "person": "John",
                        "start_time": format_time(john_start_time),
                        "end_time": format_time(john_end_time)
                    }
                    itinerary.append(meeting_with_john)
                    break
            break
    
    # Output the itinerary as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()