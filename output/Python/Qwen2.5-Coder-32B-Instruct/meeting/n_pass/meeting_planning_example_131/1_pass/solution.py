import json
from datetime import datetime, timedelta

# Constants
START_TIME = datetime.strptime("9:00", "%H:%M")
TRAVEL_TIMES = {
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Presidio"): 10
}

# Constraints
JASON_START = datetime.strptime("10:00", "%H:%M")
JASON_END = datetime.strptime("16:15", "%H:%M")
KENNETH_START = datetime.strptime("15:30", "%H:%M")
KENNETH_END = datetime.strptime("16:45", "%H:%M")

def calculate_meeting_schedule():
    current_time = START_TIME
    location = "Pacific Heights"
    itinerary = []

    # Try to meet Jason first
    if current_time + timedelta(minutes=TRAVEL_TIMES[(location, "Presidio")]) <= JASON_START:
        travel_time = TRAVEL_TIMES[(location, "Presidio")]
        current_time += timedelta(minutes=travel_time)
        location = "Presidio"

        meet_start = max(current_time, JASON_START)
        meet_end = min(meet_start + timedelta(minutes=90), JASON_END)

        if (meet_end - meet_start).total_seconds() >= 90 * 60:
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Jason",
                "start_time": meet_start.strftime("%H:%M"),
                "end_time": meet_end.strftime("%H:%M")
            })
            current_time = meet_end
            location = "Presidio"

    # Try to meet Kenneth next
    if current_time + timedelta(minutes=TRAVEL_TIMES[(location, "Marina District")]) <= KENNETH_START:
        travel_time = TRAVEL_TIMES[(location, "Marina District")]
        current_time += timedelta(minutes=travel_time)
        location = "Marina District"

        meet_start = max(current_time, KENNETH_START)
        meet_end = min(meet_start + timedelta(minutes=45), KENNETH_END)

        if (meet_end - meet_start).total_seconds() >= 45 * 60:
            itinerary.append({
                "action": "meet",
                "location": "Marina District",
                "person": "Kenneth",
                "start_time": meet_start.strftime("%H:%M"),
                "end_time": meet_end.strftime("%H:%M")
            })

    return itinerary

def main():
    itinerary = calculate_meeting_schedule()
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()