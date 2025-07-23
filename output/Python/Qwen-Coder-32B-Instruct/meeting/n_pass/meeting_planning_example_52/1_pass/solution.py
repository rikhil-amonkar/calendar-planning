import json
from datetime import datetime, timedelta

# Constants
arrival_time = datetime.strptime("9:00", "%H:%M")
travel_russian_to_richmond = timedelta(minutes=14)
travel_richmond_to_russian = timedelta(minutes=13)
barbara_start_time = datetime.strptime("13:15", "%H:%M")
barbara_end_time = datetime.strptime("18:15", "%H:%M")
min_meeting_duration = timedelta(minutes=45)

def calculate_schedule():
    current_time = arrival_time
    itinerary = []

    # Travel to Richmond District
    current_time += travel_russian_to_richmond

    # Calculate meeting time with Barbara
    meeting_start_time = max(current_time, barbara_start_time)
    meeting_end_time = min(meeting_start_time + min_meeting_duration, barbara_end_time)

    if meeting_start_time < meeting_end_time:
        itinerary.append({
            "action": "meet",
            "location": "Richmond District",
            "person": "Barbara",
            "start_time": meeting_start_time.strftime("%H:%M"),
            "end_time": meeting_end_time.strftime("%H:%M")
        })

    return itinerary

def main():
    itinerary = calculate_schedule()
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()