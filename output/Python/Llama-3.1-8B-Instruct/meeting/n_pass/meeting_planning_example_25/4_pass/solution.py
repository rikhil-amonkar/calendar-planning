import json
import datetime

def compute_meeting_schedule(arrival_time, departure_time, meeting_constraints):
    # Convert times to minutes
    arrival_minutes = int(arrival_time[:2]) * 60 + int(arrival_time[3:])
    departure_minutes = int(departure_time[:2]) * 60 + int(departure_time[3:])

    # Calculate available time for meeting
    available_time = departure_minutes - arrival_minutes

    # Initialize itinerary
    itinerary = []

    # Check if meeting with David is possible
    david_available_time = int(meeting_constraints['david_available_time'])
    david_arrival_minutes = int(meeting_constraints['david_arrival_time'][:2]) * 60 + int(meeting_constraints['david_arrival_time'][3:])
    david_departure_minutes = int(meeting_constraints['david_departure_time'][:2]) * 60 + int(meeting_constraints['david_departure_time'][3:])
    david_travel_time = int(meeting_constraints['david_travel_time'])

    # Calculate available time for meeting with David
    david_meeting_time = david_departure_minutes - david_arrival_minutes

    # Check if meeting with David is possible
    if david_arrival_minutes <= arrival_minutes and david_departure_minutes >= arrival_minutes + 105:
        # Check if meeting with David conflicts with his availability
        if david_meeting_time < 105:
            # Meeting with David conflicts with his availability, skip the meeting
            pass
        else:
            # Check if meeting with David falls within his available time
            if david_arrival_minutes + david_meeting_time <= david_departure_minutes:
                # Calculate start time for meeting with David
                start_time_minutes = max(david_arrival_minutes, arrival_minutes)
                end_time_minutes = start_time_minutes + 105
                itinerary.append({
                    "action": "meet",
                    "location": "Chinatown",
                    "person": "David",
                    "start_time": f"{start_time_minutes // 60:02d}:{start_time_minutes % 60:02d}",
                    "end_time": f"{end_time_minutes // 60:02d}:{end_time_minutes % 60:02d}"
                })
                available_time -= 105 + 2 * david_travel_time
            else:
                # Meeting with David does not fall within his available time, skip the meeting
                pass
    elif available_time >= 105 + 2 * david_travel_time:
        # Check if meeting with David conflicts with his availability
        if david_meeting_time < 105:
            # Meeting with David conflicts with his availability, skip the meeting
            pass
        else:
            # Check if meeting with David falls within his available time
            if david_arrival_minutes + david_meeting_time <= david_departure_minutes:
                # Calculate start time for meeting with David
                start_time_minutes = arrival_minutes + 105
                end_time_minutes = start_time_minutes + 105
                itinerary.append({
                    "action": "meet",
                    "location": "Chinatown",
                    "person": "David",
                    "start_time": f"{start_time_minutes // 60:02d}:{start_time_minutes % 60:02d}",
                    "end_time": f"{end_time_minutes // 60:02d}:{end_time_minutes % 60:02d}"
                })
                available_time -= 105 + 2 * david_travel_time
            else:
                # Meeting with David does not fall within his available time, skip the meeting
                pass

    # Add travel time to itinerary
    itinerary.append({
        "action": "travel",
        "location": "Chinatown",
        "person": "",
        "start_time": f"{arrival_minutes // 60:02d}:{arrival_minutes % 60:02d}",
        "end_time": f"{arrival_minutes // 60:02d}:{arrival_minutes % 60:02d}"
    })
    itinerary.append({
        "action": "travel",
        "location": "Golden Gate Park",
        "person": "",
        "start_time": f"{arrival_minutes // 60:02d}:{arrival_minutes % 60:02d}",
        "end_time": f"{arrival_minutes // 60:02d}:{arrival_minutes % 60:02d}"
    })

    # Convert itinerary to JSON
    json_itinerary = json.dumps({
        "itinerary": itinerary
    })

    return json_itinerary

def main():
    arrival_time = "09:00"
    departure_time = "23:45"
    travel_time = 23
    david_arrival_time = "16:00"
    david_departure_time = "21:45"
    david_travel_time = 23
    david_available_time = 105

    meeting_constraints = {
        "david_arrival_time": david_arrival_time,
        "david_departure_time": david_departure_time,
        "david_travel_time": str(david_travel_time),
        "david_available_time": str(david_available_time)
    }

    json_itinerary = compute_meeting_schedule(arrival_time, departure_time, meeting_constraints)
    print(json_itinerary)

if __name__ == "__main__":
    main()