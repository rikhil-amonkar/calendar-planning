import json
from datetime import datetime, timedelta

def compute_travel_time(distance):
    # Assuming a constant speed of 1 km/h (or 1 mile/h)
    return distance

def is_overlapping(start1, end1, location, meeting_time):
    """
    Checks if a meeting time overlaps with a person's available time.

    Args:
    start1 (str): The start time of the person's available time in the format "HH:MM".
    end1 (str): The end time of the person's available time in the format "HH:MM".
    location (str): The location of the meeting.
    meeting_time (str): The time of the meeting in the format "HH:MM".

    Returns:
    bool: True if the meeting time overlaps with the person's available time, False otherwise.
    """
    start1_time = datetime.strptime(start1, "%H:%M")
    end1_time = datetime.strptime(end1, "%H:%M")
    meeting_time = datetime.strptime(meeting_time, "%H:%M")

    return start1_time <= meeting_time < end1_time

def compute_meeting_schedule(
    travel_distances,
    joseph_start, joseph_end,
    jeffrey_start, jeffrey_end,
    kevin_start, kevin_end,
    david_start, david_end,
    barbara_start, barbara_end,
    min_meeting_time_joseph, min_meeting_time_jeffrey, min_meeting_time_kevin, min_meeting_time_david, min_meeting_time_barbara
):
    """
    Computes the meeting schedule for the given people.

    Args:
    travel_distances (dict): A dictionary of travel distances between locations.
    joseph_start (str): The start time of Joseph's available time in the format "HH:MM".
    joseph_end (str): The end time of Joseph's available time in the format "HH:MM".
    jeffrey_start (str): The start time of Jeffrey's available time in the format "HH:MM".
    jeffrey_end (str): The end time of Jeffrey's available time in the format "HH:MM".
    kevin_start (str): The start time of Kevin's available time in the format "HH:MM".
    kevin_end (str): The end time of Kevin's available time in the format "HH:MM".
    david_start (str): The start time of David's available time in the format "HH:MM".
    david_end (str): The end time of David's available time in the format "HH:MM".
    barbara_start (str): The start time of Barbara's available time in the format "HH:MM".
    barbara_end (str): The end time of Barbara's available time in the format "HH:MM".
    min_meeting_time_joseph (int): The minimum meeting time for Joseph in minutes.
    min_meeting_time_jeffrey (int): The minimum meeting time for Jeffrey in minutes.
    min_meeting_time_kevin (int): The minimum meeting time for Kevin in minutes.
    min_meeting_time_david (int): The minimum meeting time for David in minutes.
    min_meeting_time_barbara (int): The minimum meeting time for Barbara in minutes.

    Returns:
    list: A list of meetings in the schedule.
    """
    # Initialize the schedule
    schedule = []

    # Joseph
    joseph_available_time = (joseph_start, joseph_end)
    for location, meeting_times in travel_distances.items():
        for meeting_time in meeting_times:
            if is_overlapping(joseph_available_time[0], joseph_available_time[1], location, meeting_time):
                schedule.append({"action": "meet", "location": location, "person": "Joseph", "start_time": meeting_time, "end_time": meeting_time})
                # Update the available time
                start_time = datetime.strptime(joseph_available_time[0], "%H:%M")
                end_time = datetime.strptime(joseph_available_time[1], "%H:%M")
                meeting_start_time = datetime.strptime(meeting_time, "%H:%M")
                meeting_end_time = datetime.strptime(meeting_time, "%H:%M")
                if start_time < meeting_start_time:
                    joseph_available_time = (meeting_end_time.strftime("%H:%M"), joseph_available_time[1])
                else:
                    joseph_available_time = (joseph_available_time[0], meeting_start_time.strftime("%H:%M"))

    # Jeffrey
    jeffrey_available_time = (jeffrey_start, jeffrey_end)
    for location, meeting_times in travel_distances.items():
        for meeting_time in meeting_times:
            if is_overlapping(jeffrey_available_time[0], jeffrey_available_time[1], location, meeting_time):
                schedule.append({"action": "meet", "location": location, "person": "Jeffrey", "start_time": meeting_time, "end_time": meeting_time})
                # Update the available time
                start_time = datetime.strptime(jeffrey_available_time[0], "%H:%M")
                end_time = datetime.strptime(jeffrey_available_time[1], "%H:%M")
                meeting_start_time = datetime.strptime(meeting_time, "%H:%M")
                meeting_end_time = datetime.strptime(meeting_time, "%H:%M")
                if start_time < meeting_start_time:
                    jeffrey_available_time = (meeting_end_time.strftime("%H:%M"), jeffrey_available_time[1])
                else:
                    jeffrey_available_time = (jeffrey_available_time[0], meeting_start_time.strftime("%H:%M"))

    # Kevin
    kevin_available_time = (kevin_start, kevin_end)
    for location, meeting_times in travel_distances.items():
        for meeting_time in meeting_times:
            if is_overlapping(kevin_available_time[0], kevin_available_time[1], location, meeting_time):
                schedule.append({"action": "meet", "location": location, "person": "Kevin", "start_time": meeting_time, "end_time": meeting_time})
                # Update the available time
                start_time = datetime.strptime(kevin_available_time[0], "%H:%M")
                end_time = datetime.strptime(kevin_available_time[1], "%H:%M")
                meeting_start_time = datetime.strptime(meeting_time, "%H:%M")
                meeting_end_time = datetime.strptime(meeting_time, "%H:%M")
                if start_time < meeting_start_time:
                    kevin_available_time = (meeting_end_time.strftime("%H:%M"), kevin_available_time[1])
                else:
                    kevin_available_time = (kevin_available_time[0], meeting_start_time.strftime("%H:%M"))

    # David
    david_available_time = (david_start, david_end)
    for location, meeting_times in travel_distances.items():
        for meeting_time in meeting_times:
            if is_overlapping(david_available_time[0], david_available_time[1], location, meeting_time):
                schedule.append({"action": "meet", "location": location, "person": "David", "start_time": meeting_time, "end_time": meeting_time})
                # Update the available time
                start_time = datetime.strptime(david_available_time[0], "%H:%M")
                end_time = datetime.strptime(david_available_time[1], "%H:%M")
                meeting_start_time = datetime.strptime(meeting_time, "%H:%M")
                meeting_end_time = datetime.strptime(meeting_time, "%H:%M")
                if start_time < meeting_start_time:
                    david_available_time = (meeting_end_time.strftime("%H:%M"), david_available_time[1])
                else:
                    david_available_time = (david_available_time[0], meeting_start_time.strftime("%H:%M"))

    # Barbara
    barbara_available_time = (barbara_start, barbara_end)
    for location, meeting_times in travel_distances.items():
        for meeting_time in meeting_times:
            if is_overlapping(barbara_available_time[0], barbara_available_time[1], location, meeting_time):
                schedule.append({"action": "meet", "location": location, "person": "Barbara", "start_time": meeting_time, "end_time": meeting_time})
                # Update the available time
                start_time = datetime.strptime(barbara_available_time[0], "%H:%M")
                end_time = datetime.strptime(barbara_available_time[1], "%H:%M")
                meeting_start_time = datetime.strptime(meeting_time, "%H:%M")
                meeting_end_time = datetime.strptime(meeting_time, "%H:%M")
                if start_time < meeting_start_time:
                    barbara_available_time = (meeting_end_time.strftime("%H:%M"), barbara_available_time[1])
                else:
                    barbara_available_time = (barbara_available_time[0], meeting_start_time.strftime("%H:%M"))

    return schedule

def main():
    travel_distances = {
        "Golden Gate Park": {
            "Fisherman's Wharf": 24,
            "Bayview": 23,
            "Mission District": 17,
            "Embarcadero": 25,
            "Financial District": 26,
        },
        "Fisherman's Wharf": {
            "Golden Gate Park": 25,
            "Bayview": 26,
            "Mission District": 22,
            "Embarcadero": 8,
            "Financial District": 11,
        },
        "Bayview": {
            "Golden Gate Park": 22,
            "Fisherman's Wharf": 25,
            "Mission District": 13,
            "Embarcadero": 19,
            "Financial District": 19,
        },
        "Mission District": {
            "Golden Gate Park": 17,
            "Fisherman's Wharf": 22,
            "Bayview": 15,
            "Embarcadero": 19,
            "Financial District": 17,
        },
        "Embarcadero": {
            "Golden Gate Park": 25,
            "Fisherman's Wharf": 6,
            "Bayview": 21,
            "Mission District": 20,
            "Financial District": 5,
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Fisherman's Wharf": 10,
            "Bayview": 19,
            "Mission District": 17,
            "Embarcadero": 4,
        },
    }

    joseph_start = "08:00"
    joseph_end = "05:30"
    jeffrey_start = "17:30"
    jeffrey_end = "21:30"
    kevin_start = "11:15"
    kevin_end = "15:15"
    david_start = "08:15"
    david_end = "09:00"
    barbara_start = "10:30"
    barbara_end = "16:30"

    min_meeting_time_joseph = 90
    min_meeting_time_jeffrey = 60
    min_meeting_time_kevin = 30
    min_meeting_time_david = 30
    min_meeting_time_barbara = 15

    schedule = compute_meeting_schedule(
        travel_distances,
        joseph_start, joseph_end,
        jeffrey_start, jeffrey_end,
        kevin_start, kevin_end,
        david_start, david_end,
        barbara_start, barbara_end,
        min_meeting_time_joseph, min_meeting_time_jeffrey, min_meeting_time_kevin, min_meeting_time_david, min_meeting_time_barbara
    )

    # Convert the schedule to a JSON-formatted string
    json_schedule = json.dumps(schedule, indent=4)

    print("SOLUTION:")
    print(json_schedule)

if __name__ == "__main__":
    main()