import json
from datetime import datetime, timedelta

def compute_meeting_schedule(arrival_time, departure_time, travel_time, meeting_duration, person_name, location):
    start_time = datetime.strptime(arrival_time, "%H:%M")
    end_time = datetime.strptime(departure_time, "%H:%M")
    travel_duration = timedelta(minutes=travel_time)
    meeting_duration = timedelta(minutes=meeting_duration)

    # Find the earliest possible meeting time
    earliest_meeting_time = start_time + travel_duration
    if earliest_meeting_time < start_time:
        earliest_meeting_time = start_time

    # Find the latest possible meeting time
    latest_meeting_time = end_time - travel_duration - meeting_duration
    if latest_meeting_time > end_time:
        latest_meeting_time = end_time

    # Check if a meeting is possible
    if earliest_meeting_time <= latest_meeting_time:
        # Calculate the optimal meeting time
        optimal_meeting_time = earliest_meeting_time
        optimal_meeting_end_time = optimal_meeting_time + meeting_duration
        return {
            "action": "meet",
            "location": location,
            "person": person_name,
            "start_time": optimal_meeting_time.strftime("%H:%M"),
            "end_time": optimal_meeting_end_time.strftime("%H:%M")
        }
    else:
        return None

def generate_meeting_schedule():
    arrival_time = "09:00"
    departure_time = "20:15"
    travel_time = 14
    meeting_duration = 75
    person_name = "Daniel"
    location = "Richmond District"

    # Compute the schedule
    schedule = []
    schedule.append(compute_meeting_schedule(arrival_time, departure_time, travel_time, meeting_duration, person_name, location))

    # Compute the return trip
    travel_time = 13
    schedule.append({
        "action": "travel",
        "location": "Richmond District",
        "person": "You",
        "start_time": schedule[-1]["end_time"],
        "end_time": (datetime.strptime(schedule[-1]["end_time"], "%H:%M") + timedelta(minutes=travel_time)).strftime("%H:%M")
    })

    # Add the return trip to the location of arrival
    schedule.append({
        "action": "return",
        "location": "Russian Hill",
        "person": "You",
        "start_time": schedule[-1]["end_time"],
        "end_time": (datetime.strptime(schedule[-1]["end_time"], "%H:%M") + timedelta(minutes=travel_time)).strftime("%H:%M")
    })

    return schedule

def main():
    schedule = generate_meeting_schedule()
    itinerary = {"itinerary": schedule}
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()