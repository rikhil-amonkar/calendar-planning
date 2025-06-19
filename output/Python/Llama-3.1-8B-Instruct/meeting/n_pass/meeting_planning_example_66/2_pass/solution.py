import json
from datetime import datetime, timedelta

def calculate_travel_time(distance, start_time):
    """
    Calculate the end time of a travel action given the distance and start time.

    Args:
        distance (int): The distance of the travel in minutes.
        start_time (datetime): The start time of the travel.

    Returns:
        datetime: The end time of the travel.
    """
    travel_time = timedelta(minutes=distance)
    end_time = start_time + travel_time
    return end_time

def compute_optimal_schedule(arrival_time, constraints):
    """
    Compute the optimal schedule given the arrival time and constraints.

    Args:
        arrival_time (datetime): The arrival time.
        constraints (dict): A dictionary containing the constraints.

    Returns:
        list: A list of actions in the optimal schedule.
    """
    optimal_schedule = []
    nob_hill = "Nob Hill"
    presidio = "Presidio"

    # Meeting Robert at Presidio from 11:15AM to 5:45PM
    start_time = datetime.strptime("11:15", "%H:%M")
    end_time = datetime.strptime("5:45", "%H:%M")

    # Ensure we arrive before Robert starts
    if start_time < arrival_time + timedelta(hours=1):
        # Calculate earliest meeting time
        earliest_meeting_time = max(start_time, arrival_time + timedelta(minutes=17))

        # Check if meeting Robert for 120 minutes is possible
        if end_time - earliest_meeting_time >= timedelta(minutes=120):
            # Add meeting to schedule
            optimal_schedule.append({
                "action": "meet",
                "location": presidio,
                "person": "Robert",
                "start_time": earliest_meeting_time.strftime("%H:%M"),
                "end_time": (earliest_meeting_time + timedelta(minutes=120)).strftime("%H:%M")
            })

    # Add travel to schedule
    if optimal_schedule:
        optimal_schedule.insert(0, {
            "action": "travel",
            "location": "Presidio",
            "person": "None",
            "start_time": (arrival_time + timedelta(minutes=17)).strftime("%H:%M"),
            "end_time": (arrival_time + timedelta(minutes=17)).strftime("%H:%M")
        })

        optimal_schedule.append({
            "action": "travel",
            "location": nob_hill,
            "person": "None",
            "start_time": (end_time + timedelta(minutes=18)).strftime("%H:%M"),
            "end_time": (end_time + timedelta(minutes=18)).strftime("%H:%M")
        })

    return optimal_schedule

def main():
    try:
        arrival_time = datetime.strptime("09:00", "%H:%M")
        nob_hill_to_presidio = 17
        presidio_to_nob_hill = 18
        robert_start_time = datetime.strptime("11:15", "%H:%M")
        robert_end_time = datetime.strptime("5:45", "%H:%M")
        min_meeting_duration = 120

        # Validate input constraints
        if nob_hill_to_presidio < 0 or presidio_to_nob_hill < 0:
            raise ValueError("Travel distances cannot be negative")

        # Calculate optimal schedule
        optimal_schedule = compute_optimal_schedule(arrival_time, {
            "robert_start_time": robert_start_time,
            "robert_end_time": robert_end_time,
            "min_meeting_duration": min_meeting_duration
        })

        # Output schedule as JSON
        print(json.dumps({"itinerary": optimal_schedule}, indent=4))

    except ValueError as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    main()