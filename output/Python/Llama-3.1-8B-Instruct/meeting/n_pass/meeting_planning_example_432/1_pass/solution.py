import json
from datetime import datetime, timedelta

def compute_travel_time(distance):
    # Assuming a constant speed of 1 km/h (or 1 mile/h)
    return distance

def is_overlapping(start1, end1, start2, end2):
    return start1 <= end2 and start2 <= end1

def compute_meeting_schedule(
    travel_distances,
    joseph_start, joseph_end,
    jeffrey_start, jeffrey_end,
    kevin_start, kevin_end,
    david_start, david_end,
    barbara_start, barbara_end,
    min_meeting_time_joseph, min_meeting_time_jeffrey, min_meeting_time_kevin, min_meeting_time_david, min_meeting_time_barbara
):
    # Initialize the schedule
    schedule = []

    # Joseph
    joseph_available_time = (joseph_start, joseph_end)
    if is_overlapping(joseph_available_time, "09:00", "09:30"):  # Golden Gate Park
        schedule.append({"action": "meet", "location": "Golden Gate Park", "person": "Joseph", "start_time": "09:00", "end_time": "09:30"})
        joseph_available_time = (joseph_available_time[0], "09:30")
    if is_overlapping(joseph_available_time, "10:00", "10:30"):  # Fisherman's Wharf
        schedule.append({"action": "meet", "location": "Fisherman's Wharf", "person": "Joseph", "start_time": "10:00", "end_time": "10:30"})
        joseph_available_time = (joseph_available_time[0], "10:30")
    if is_overlapping(joseph_available_time, "11:00", "11:30"):  # Mission District
        schedule.append({"action": "meet", "location": "Mission District", "person": "Joseph", "start_time": "11:00", "end_time": "11:30"})
        joseph_available_time = (joseph_available_time[0], "11:30")
    if is_overlapping(joseph_available_time, "12:00", "12:30"):  # Bayview
        schedule.append({"action": "meet", "location": "Bayview", "person": "Joseph", "start_time": "12:00", "end_time": "12:30"})
        joseph_available_time = (joseph_available_time[0], "12:30")
    if is_overlapping(joseph_available_time, "13:00", "13:30"):  # Embarcadero
        schedule.append({"action": "meet", "location": "Embarcadero", "person": "Joseph", "start_time": "13:00", "end_time": "13:30"})
        joseph_available_time = (joseph_available_time[0], "13:30")
    if is_overlapping(joseph_available_time, "14:00", "14:30"):  # Financial District
        schedule.append({"action": "meet", "location": "Financial District", "person": "Joseph", "start_time": "14:00", "end_time": "14:30"})
        joseph_available_time = (joseph_available_time[0], "14:30")

    # Jeffrey
    jeffrey_available_time = (jeffrey_start, jeffrey_end)
    if is_overlapping(jeffrey_available_time, "17:30", "18:00"):  # Golden Gate Park
        schedule.append({"action": "meet", "location": "Golden Gate Park", "person": "Jeffrey", "start_time": "17:30", "end_time": "18:00"})
        jeffrey_available_time = (jeffrey_available_time[0], "18:00")
    if is_overlapping(jeffrey_available_time, "18:00", "18:30"):  # Fisherman's Wharf
        schedule.append({"action": "meet", "location": "Fisherman's Wharf", "person": "Jeffrey", "start_time": "18:00", "end_time": "18:30"})
        jeffrey_available_time = (jeffrey_available_time[0], "18:30")
    if is_overlapping(jeffrey_available_time, "18:30", "19:00"):  # Mission District
        schedule.append({"action": "meet", "location": "Mission District", "person": "Jeffrey", "start_time": "18:30", "end_time": "19:00"})
        jeffrey_available_time = (jeffrey_available_time[0], "19:00")
    if is_overlapping(jeffrey_available_time, "19:00", "19:30"):  # Bayview
        schedule.append({"action": "meet", "location": "Bayview", "person": "Jeffrey", "start_time": "19:00", "end_time": "19:30"})
        jeffrey_available_time = (jeffrey_available_time[0], "19:30")
    if is_overlapping(jeffrey_available_time, "19:30", "20:00"):  # Embarcadero
        schedule.append({"action": "meet", "location": "Embarcadero", "person": "Jeffrey", "start_time": "19:30", "end_time": "20:00"})
        jeffrey_available_time = (jeffrey_available_time[0], "20:00")
    if is_overlapping(jeffrey_available_time, "20:00", "20:30"):  # Financial District
        schedule.append({"action": "meet", "location": "Financial District", "person": "Jeffrey", "start_time": "20:00", "end_time": "20:30"})
        jeffrey_available_time = (jeffrey_available_time[0], "20:30")

    # Kevin
    kevin_available_time = (kevin_start, kevin_end)
    if is_overlapping(kevin_available_time, "11:15", "11:45"):  # Golden Gate Park
        schedule.append({"action": "meet", "location": "Golden Gate Park", "person": "Kevin", "start_time": "11:15", "end_time": "11:45"})
        kevin_available_time = (kevin_available_time[0], "11:45")
    if is_overlapping(kevin_available_time, "12:00", "12:30"):  # Fisherman's Wharf
        schedule.append({"action": "meet", "location": "Fisherman's Wharf", "person": "Kevin", "start_time": "12:00", "end_time": "12:30"})
        kevin_available_time = (kevin_available_time[0], "12:30")
    if is_overlapping(kevin_available_time, "12:30", "13:00"):  # Mission District
        schedule.append({"action": "meet", "location": "Mission District", "person": "Kevin", "start_time": "12:30", "end_time": "13:00"})
        kevin_available_time = (kevin_available_time[0], "13:00")
    if is_overlapping(kevin_available_time, "13:00", "13:30"):  # Bayview
        schedule.append({"action": "meet", "location": "Bayview", "person": "Kevin", "start_time": "13:00", "end_time": "13:30"})
        kevin_available_time = (kevin_available_time[0], "13:30")
    if is_overlapping(kevin_available_time, "13:30", "14:00"):  # Embarcadero
        schedule.append({"action": "meet", "location": "Embarcadero", "person": "Kevin", "start_time": "13:30", "end_time": "14:00"})
        kevin_available_time = (kevin_available_time[0], "14:00")
    if is_overlapping(kevin_available_time, "14:00", "14:30"):  # Financial District
        schedule.append({"action": "meet", "location": "Financial District", "person": "Kevin", "start_time": "14:00", "end_time": "14:30"})
        kevin_available_time = (kevin_available_time[0], "14:30")

    # David
    david_available_time = (david_start, david_end)
    if is_overlapping(david_available_time, "08:15", "08:45"):  # Golden Gate Park
        schedule.append({"action": "meet", "location": "Golden Gate Park", "person": "David", "start_time": "08:15", "end_time": "08:45"})
        david_available_time = (david_available_time[0], "08:45")
    if is_overlapping(david_available_time, "08:45", "09:00"):  # Embarcadero
        schedule.append({"action": "meet", "location": "Embarcadero", "person": "David", "start_time": "08:45", "end_time": "09:00"})
        david_available_time = (david_available_time[0], "09:00")

    # Barbara
    barbara_available_time = (barbara_start, barbara_end)
    if is_overlapping(barbara_available_time, "10:30", "10:45"):  # Golden Gate Park
        schedule.append({"action": "meet", "location": "Golden Gate Park", "person": "Barbara", "start_time": "10:30", "end_time": "10:45"})
        barbara_available_time = (barbara_available_time[0], "10:45")
    if is_overlapping(barbara_available_time, "10:45", "11:00"):  # Financial District
        schedule.append({"action": "meet", "location": "Financial District", "person": "Barbara", "start_time": "10:45", "end_time": "11:00"})
        barbara_available_time = (barbara_available_time[0], "11:00")
    if is_overlapping(barbara_available_time, "11:00", "11:15"):  # Embarcadero
        schedule.append({"action": "meet", "location": "Embarcadero", "person": "Barbara", "start_time": "11:00", "end_time": "11:15"})
        barbara_available_time = (barbara_available_time[0], "11:15")
    if is_overlapping(barbara_available_time, "11:15", "11:30"):  # Mission District
        schedule.append({"action": "meet", "location": "Mission District", "person": "Barbara", "start_time": "11:15", "end_time": "11:30"})
        barbara_available_time = (barbara_available_time[0], "11:30")
    if is_overlapping(barbara_available_time, "11:30", "11:45"):  # Bayview
        schedule.append({"action": "meet", "location": "Bayview", "person": "Barbara", "start_time": "11:30", "end_time": "11:45"})
        barbara_available_time = (barbara_available_time[0], "11:45")
    if is_overlapping(barbara_available_time, "11:45", "12:00"):  # Fisherman's Wharf
        schedule.append({"action": "meet", "location": "Fisherman's Wharf", "person": "Barbara", "start_time": "11:45", "end_time": "12:00"})
        barbara_available_time = (barbara_available_time[0], "12:00")
    if is_overlapping(barbara_available_time, "12:00", "12:15"):  # Embarcadero
        schedule.append({"action": "meet", "location": "Embarcadero", "person": "Barbara", "start_time": "12:00", "end_time": "12:15"})
        barbara_available_time = (barbara_available_time[0], "12:15")
    if is_overlapping(barbara_available_time, "12:15", "12:30"):  # Financial District
        schedule.append({"action": "meet", "location": "Financial District", "person": "Barbara", "start_time": "12:15", "end_time": "12:30"})
        barbara_available_time = (barbara_available_time[0], "12:30")
    if is_overlapping(barbara_available_time, "12:30", "12:45"):  # Mission District
        schedule.append({"action": "meet", "location": "Mission District", "person": "Barbara", "start_time": "12:30", "end_time": "12:45"})
        barbara_available_time = (barbara_available_time[0], "12:45")
    if is_overlapping(barbara_available_time, "12:45", "13:00"):  # Bayview
        schedule.append({"action": "meet", "location": "Bayview", "person": "Barbara", "start_time": "12:45", "end_time": "13:00"})
        barbara_available_time = (barbara_available_time[0], "13:00")
    if is_overlapping(barbara_available_time, "13:00", "13:15"):  # Fisherman's Wharf
        schedule.append({"action": "meet", "location": "Fisherman's Wharf", "person": "Barbara", "start_time": "13:00", "end_time": "13:15"})
        barbara_available_time = (barbara_available_time[0], "13:15")
    if is_overlapping(barbara_available_time, "13:15", "13:30"):  # Embarcadero
        schedule.append({"action": "meet", "location": "Embarcadero", "person": "Barbara", "start_time": "13:15", "end_time": "13:30"})
        barbara_available_time = (barbara_available_time[0], "13:30")
    if is_overlapping(barbara_available_time, "13:30", "13:45"):  # Financial District
        schedule.append({"action": "meet", "location": "Financial District", "person": "Barbara", "start_time": "13:30", "end_time": "13:45"})
        barbara_available_time = (barbara_available_time[0], "13:45")
    if is_overlapping(barbara_available_time, "13:45", "14:00"):  # Mission District
        schedule.append({"action": "meet", "location": "Mission District", "person": "Barbara", "start_time": "13:45", "end_time": "14:00"})
        barbara_available_time = (barbara_available_time[0], "14:00")
    if is_overlapping(barbara_available_time, "14:00", "14:15"):  # Bayview
        schedule.append({"action": "meet", "location": "Bayview", "person": "Barbara", "start_time": "14:00", "end_time": "14:15"})
        barbara_available_time = (barbara_available_time[0], "14:15")
    if is_overlapping(barbara_available_time, "14:15", "14:30"):  # Fisherman's Wharf
        schedule.append({"action": "meet", "location": "Fisherman's Wharf", "person": "Barbara", "start_time": "14:15", "end_time": "14:30"})
        barbara_available_time = (barbara_available_time[0], "14:30")

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