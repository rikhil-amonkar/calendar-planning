import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def calculate_schedule():
    # Define travel times
    travel_times = {
        ('richmond district', 'pacific heights'): 10,
        ('richmond district', 'marina district'): 9,
        ('pacific heights', 'richmond district'): 12,
        ('pacific heights', 'marina district'): 6,
        ('marina district', 'richmond district'): 11,
        ('marina district', 'pacific heights'): 7
    }

    # Define constraints
    start_time = parse_time('9:00')
    jessica_start = parse_time('15:30')
    jessica_end = parse_time('16:45')
    carol_start = parse_time('11:30')
    carol_end = parse_time('15:00')

    # Minimum meeting durations
    min_meeting_jessica = timedelta(minutes=45)
    min_meeting_carol = timedelta(minutes=60)

    # Possible meeting slots
    carol_slot = (carol_start, carol_end - min_meeting_carol)
    jessica_slot = (jessica_start, jessica_end - min_meeting_jessica)

    # Function to check if a slot is available after traveling
    def is_slot_available(current_time, location, slot, destination):
        travel_time = travel_times.get((location, destination), float('inf'))
        arrival_time = current_time + timedelta(minutes=travel_time)
        return arrival_time <= slot[1]

    # Try to fit meetings into the schedule
    itinerary = []
    current_time = start_time
    current_location = 'richmond district'

    # Try to meet Carol first
    if is_slot_available(current_time, current_location, carol_slot, 'marina district'):
        travel_time = travel_times[(current_location, 'marina district')]
        meet_start = current_time + timedelta(minutes=travel_time)
        meet_end = meet_start + min_meeting_carol
        itinerary.append({
            "action": "meet",
            "location": "Marina District",
            "person": "Carol",
            "start_time": format_time(meet_start),
            "end_time": format_time(meet_end)
        })
        current_time = meet_end
        current_location = 'marina district'

    # Try to meet Jessica next
    if is_slot_available(current_time, current_location, jessica_slot, 'pacific heights'):
        travel_time = travel_times[(current_location, 'pacific heights')]
        meet_start = current_time + timedelta(minutes=travel_time)
        meet_end = meet_start + min_meeting_jessica
        itinerary.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Jessica",
            "start_time": format_time(meet_start),
            "end_time": format_time(meet_end)
        })

    # Output the itinerary as JSON
    print(json.dumps({"itinerary": itinerary}))

calculate_schedule()