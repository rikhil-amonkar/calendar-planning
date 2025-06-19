import json
from datetime import datetime, timedelta

def compute_travel_time(origin, destination, travel_times):
    """
    Compute the travel time between two locations.

    Args:
    origin (str): The origin location.
    destination (str): The destination location.
    travel_times (dict): A dictionary of travel times between locations.

    Returns:
    int: The travel time between the origin and destination locations.
    """
    return travel_times[f"{origin}-{destination}"]

def compute_meeting_schedule(arrival_time, thomas_constraints, kenneth_constraints, travel_times):
    """
    Compute the meeting schedule based on the arrival time, Thomas' constraints, Kenneth's constraints, and travel times.

    Args:
    arrival_time (str): The arrival time in the format "HH:MM".
    thomas_constraints (dict): A dictionary of Thomas' constraints.
    kenneth_constraints (dict): A dictionary of Kenneth's constraints.
    travel_times (dict): A dictionary of travel times between locations.

    Returns:
    list: A list of meeting schedules in the format {"action": "meet", "location": "location", "person": "person", "start_time": "start_time", "end_time": "end_time"}.
    """
    schedule = []
    current_time = datetime.strptime(arrival_time, "%H:%M")

    # Meet Thomas
    thomas_travel_time = compute_travel_time('Nob Hill', 'Pacific Heights', travel_times)
    thomas_meeting_time = max(datetime.strptime(thomas_constraints['start_time'], "%H:%M"), current_time + timedelta(minutes=thomas_travel_time))
    thomas_meeting_end_time = thomas_meeting_time + timedelta(minutes=75)

    if thomas_meeting_time < datetime.strptime(thomas_constraints['end_time'], "%H:%M") and thomas_meeting_end_time <= datetime.strptime(thomas_constraints['end_time'], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Thomas",
            "start_time": thomas_meeting_time.strftime("%H:%M"),
            "end_time": thomas_meeting_end_time.strftime("%H:%M")
        })
        current_time = thomas_meeting_end_time
        print(f"Met Thomas at {thomas_meeting_time.strftime('%H:%M')} and ended at {thomas_meeting_end_time.strftime('%H:%M')}")
    else:
        print("Could not meet Thomas within his constraints.")

    # Meet Kenneth
    kenneth_travel_time = compute_travel_time('Nob Hill', 'Mission District', travel_times)
    kenneth_meeting_time = max(datetime.strptime(kenneth_constraints['start_time'], "%H:%M"), current_time + timedelta(minutes=kenneth_travel_time))
    kenneth_meeting_end_time = kenneth_meeting_time + timedelta(minutes=45)

    if kenneth_meeting_time < datetime.strptime(kenneth_constraints['end_time'], "%H:%M") and kenneth_meeting_end_time <= datetime.strptime(kenneth_constraints['end_time'], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Kenneth",
            "start_time": kenneth_meeting_time.strftime("%H:%M"),
            "end_time": kenneth_meeting_end_time.strftime("%H:%M")
        })
        current_time = kenneth_meeting_end_time
        print(f"Met Kenneth at {kenneth_meeting_time.strftime('%H:%M')} and ended at {kenneth_meeting_end_time.strftime('%H:%M')}")
    else:
        print("Could not meet Kenneth within his constraints.")

    return schedule

def main():
    travel_times = {
        "Nob Hill-Pacific Heights": 8,
        "Nob Hill-Mission District": 13,
        "Pacific Heights-Nob Hill": 8,
        "Pacific Heights-Mission District": 15,
        "Mission District-Nob Hill": 12,
        "Mission District-Pacific Heights": 16
    }

    arrival_time = "09:00"
    thomas_constraints = {
        "start_time": "15:30",
        "end_time": "19:15"
    }
    kenneth_constraints = {
        "start_time": "12:00",
        "end_time": "15:45"
    }

    schedule = compute_meeting_schedule(arrival_time, thomas_constraints, kenneth_constraints, travel_times)

    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()