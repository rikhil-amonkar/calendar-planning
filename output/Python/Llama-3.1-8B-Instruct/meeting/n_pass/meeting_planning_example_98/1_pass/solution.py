import json
from datetime import datetime, timedelta

def calculate_travel_time(distance):
    return distance // 60

def compute_optimal_schedule(arrival_time, meeting_constraints):
    # Convert arrival time to datetime object
    arrival_time = datetime.strptime(arrival_time, "%H:%M")

    # Initialize schedule and current time
    schedule = []
    current_time = arrival_time

    # Process each meeting constraint
    for person, time_range, min_meeting_time, location in meeting_constraints:
        # Calculate travel time
        travel_time = calculate_travel_time(12)

        # Calculate start and end times for meeting
        start_time = time_range[0] - timedelta(minutes=travel_time)
        end_time = time_range[1] + timedelta(minutes=travel_time)

        # Check if meeting is possible
        if start_time < current_time or end_time < current_time:
            continue

        # Add meeting to schedule
        schedule.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })

        # Update current time
        current_time = end_time + timedelta(minutes=min_meeting_time)

    return schedule

def main():
    # Define meeting constraints
    meeting_constraints = [
        ("Timothy", ("20:45", "21:30"), 45, "Richmond District")
    ]

    # Define travel distances
    travel_distances = {
        "Alamo Square to Richmond District": 12,
        "Richmond District to Alamo Square": 13
    }

    # Define arrival time
    arrival_time = "09:00"

    # Compute optimal schedule
    schedule = compute_optimal_schedule(arrival_time, meeting_constraints)

    # Print schedule as JSON
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()