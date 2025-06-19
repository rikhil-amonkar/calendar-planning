import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Golden Gate Park"): 17,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17
}

# Constraints
start_time = datetime.strptime("09:00", "%H:%M")
sarah_start = datetime.strptime("10:45", "%H:%M")
sarah_end = datetime.strptime("19:00", "%H:%M")
richard_start = datetime.strptime("11:45", "%H:%M")
richard_end = datetime.strptime("15:45", "%H:%M")
elizabeth_start = datetime.strptime("11:00", "%H:%M")
elizabeth_end = datetime.strptime("17:15", "%H:%M")
michelle_start = datetime.strptime("18:15", "%H:%M")
michelle_end = datetime.strptime("20:45", "%H:%M")

# Minimum meeting times
min_meeting_times = {
    "Sarah": timedelta(minutes=30),
    "Richard": timedelta(hours=1.5),
    "Elizabeth": timedelta(hours=2),
    "Michelle": timedelta(hours=1.5)
}

def calculate_meeting_time(start_time, end_time, travel_time):
    return max(0, (end_time - start_time) - travel_time)

def compute_schedule():
    schedule = []
    current_time = start_time
    
    # Meet Sarah
    travel_time = timedelta(minutes=travel_distances[("Richmond District", "Sunset District")])
    meeting_time = calculate_meeting_time(current_time, sarah_start, travel_time)
    if meeting_time >= min_meeting_times["Sarah"]:
        schedule.append({
            "action": "meet",
            "location": "Sunset District",
            "person": "Sarah",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Sarah"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Sarah"] + travel_time
        current_time += timedelta(minutes=30)  # Wait for Sarah to be available
    
    # Meet Richard
    travel_time = timedelta(minutes=travel_distances[("Sunset District", "Haight-Ashbury")])
    meeting_time = calculate_meeting_time(current_time, richard_start, travel_time)
    if meeting_time >= min_meeting_times["Richard"]:
        schedule.append({
            "action": "meet",
            "location": "Haight-Ashbury",
            "person": "Richard",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Richard"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Richard"] + travel_time
        current_time += timedelta(hours=1)  # Wait for Richard to be available
    
    # Meet Elizabeth
    travel_time = timedelta(minutes=travel_distances[("Haight-Ashbury", "Mission District")])
    meeting_time = calculate_meeting_time(current_time, elizabeth_start, travel_time)
    if meeting_time >= min_meeting_times["Elizabeth"]:
        schedule.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Elizabeth",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Elizabeth"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Elizabeth"] + travel_time
        current_time += timedelta(hours=1)  # Wait for Elizabeth to be available
    
    # Meet Michelle
    travel_time = timedelta(minutes=travel_distances[("Mission District", "Golden Gate Park")])
    meeting_time = calculate_meeting_time(current_time, michelle_start, travel_time)
    if meeting_time >= min_meeting_times["Michelle"]:
        schedule.append({
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Michelle",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Michelle"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Michelle"] + travel_time
    
    return schedule

def main():
    schedule = compute_schedule()
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()