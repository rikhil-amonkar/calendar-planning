import json
from datetime import datetime, timedelta

def compute_travel_time(distance):
    return distance // 10  # assuming 10 minutes per unit

def compute_meeting_schedule(arrival_time, joshua_start_time, joshua_end_time, travel_distance):
    # Convert times to datetime objects
    arrival_time = datetime.strptime(arrival_time, "%H:%M")
    joshua_start_time = datetime.strptime(joshua_start_time, "%H:%M")
    joshua_end_time = datetime.strptime(joshua_end_time, "%H:%M")

    # Calculate travel time from arrival location to Golden Gate Park
    travel_time_to_ggp = compute_travel_time(travel_distance)

    # Calculate travel time from Golden Gate Park back to Sunset District
    travel_time_from_ggp = compute_travel_time(travel_distance)

    # Calculate earliest possible meeting time
    earliest_meeting_time = max(joshua_start_time, arrival_time + timedelta(minutes=travel_time_to_ggp))

    # Check if meeting can be scheduled
    if earliest_meeting_time + timedelta(minutes=15) <= joshua_end_time:
        # Calculate end time of meeting
        end_time = earliest_meeting_time + timedelta(minutes=15)

        # Create meeting schedule
        itinerary = [
            {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Joshua",
                "start_time": earliest_meeting_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M")
            },
            {
                "action": "travel",
                "location": "Golden Gate Park",
                "person": "You",
                "start_time": (earliest_meeting_time - timedelta(minutes=travel_time_to_ggp)).strftime("%H:%M"),
                "end_time": earliest_meeting_time.strftime("%H:%M")
            },
            {
                "action": "travel",
                "location": "Sunset District",
                "person": "You",
                "start_time": end_time.strftime("%H:%M"),
                "end_time": (end_time + timedelta(minutes=travel_time_from_ggp)).strftime("%H:%M")
            }
        ]
    else:
        itinerary = []

    return itinerary

def main():
    arrival_time = "09:00"
    joshua_start_time = "20:45"
    joshua_end_time = "21:45"
    travel_distance = 11  # Sunset District to Golden Gate Park

    itinerary = compute_meeting_schedule(arrival_time, joshua_start_time, joshua_end_time, travel_distance)

    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()