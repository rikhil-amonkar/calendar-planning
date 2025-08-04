import json
from datetime import datetime, timedelta

def calculate_schedule():
    # Constants
    arrival_time = datetime.strptime("9:00", "%H:%M")
    travel_time = timedelta(minutes=23)
    david_start = datetime.strptime("16:00", "%H:%M")
    david_end = datetime.strptime("21:45", "%H:%M")
    min_meeting_duration = timedelta(minutes=105)

    # Calculate the latest time we can start meeting David
    latest_start_with_david = david_end - min_meeting_duration

    # Determine if we can meet David
    if latest_start_with_david >= david_start:
        # We can meet David, calculate the meeting time
        meeting_start = max(david_start, latest_start_with_david)
        meeting_end = meeting_start + min_meeting_duration

        itinerary = [
            {
                "action": "meet",
                "location": "Chinatown",
                "person": "David",
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            }
        ]
    else:
        # Cannot meet David for the required duration
        itinerary = []

    return {
        "itinerary": itinerary
    }

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule))