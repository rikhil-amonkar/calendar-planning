import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Financial District"): 23,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Financial District"): 22,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21
}

# Define meeting constraints
meetings = {
    "Emily": {"location": "Presidio", "start": "16:15", "end": "21:00", "min_duration": 105},
    "Joseph": {"location": "Richmond District", "start": "17:15", "end": "22:00", "min_duration": 120},
    "Melissa": {"location": "Financial District", "start": "15:45", "end": "21:45", "min_duration": 75}
}

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M").lstrip('0')

def calculate_schedule():
    start_time = parse_time("9:00")
    current_location = "Fisherman's Wharf"
    itinerary = []

    # Sort meetings by earliest start time
    sorted_meetings = sorted(meetings.items(), key=lambda x: parse_time(x[1]['start']))

    for name, details in sorted_meetings:
        location = details['location']
        start = parse_time(details['start'])
        end = parse_time(details['end'])
        min_duration = timedelta(minutes=details['min_duration'])

        # Calculate travel time
        travel_time = timedelta(minutes=travel_times[(current_location, location)])
        arrival_time = start_time + travel_time

        # Adjust arrival time if it's before the meeting starts
        if arrival_time < start:
            arrival_time = start

        # Calculate meeting end time
        meeting_end_time = arrival_time + min_duration

        # Check if meeting can fit within the person's availability
        if meeting_end_time <= end:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": format_time(arrival_time),
                "end_time": format_time(meeting_end_time)
            })
            start_time = meeting_end_time
            current_location = location
        else:
            # If the meeting cannot fit, skip this person
            continue

    return itinerary

def main():
    itinerary = calculate_schedule()
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()