import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Bayview": {
        "Pacific Heights": 23,
        "Mission District": 13,
        "Haight-Ashbury": 19,
        "Financial District": 19
    },
    "Pacific Heights": {
        "Bayview": 22,
        "Mission District": 15,
        "Haight-Ashbury": 11,
        "Financial District": 13
    },
    "Mission District": {
        "Bayview": 15,
        "Pacific Heights": 16,
        "Haight-Ashbury": 12,
        "Financial District": 17
    },
    "Haight-Ashbury": {
        "Bayview": 18,
        "Pacific Heights": 12,
        "Mission District": 11,
        "Financial District": 21
    },
    "Financial District": {
        "Bayview": 19,
        "Pacific Heights": 13,
        "Mission District": 17,
        "Haight-Ashbury": 19
    }
}

# Constraints
start_time = datetime.strptime("09:00", "%H:%M")
mary_start_time = datetime.strptime("10:00", "%H:%M")
mary_end_time = datetime.strptime("19:00", "%H:%M")
lisa_start_time = datetime.strptime("20:30", "%H:%M")
lisa_end_time = datetime.strptime("22:00", "%H:%M")
betty_start_time = datetime.strptime("07:15", "%H:%M")
betty_end_time = datetime.strptime("17:15", "%H:%M")
charles_start_time = datetime.strptime("11:15", "%H:%M")
charles_end_time = datetime.strptime("15:00", "%H:%M")

# Minimum meeting times
min_meeting_times = {
    "Mary": timedelta(minutes=45),
    "Lisa": timedelta(minutes=75),
    "Betty": timedelta(minutes=90),
    "Charles": timedelta(minutes=120)
}

def compute_travel_time(start_location, end_location):
    return timedelta(minutes=travel_distances[start_location][end_location])

def compute_meeting_schedule():
    schedule = []
    current_time = start_time
    meeting_locations = {
        "Mary": "Pacific Heights",
        "Lisa": "Mission District",
        "Betty": "Haight-Ashbury",
        "Charles": "Financial District"
    }

    # Meet Betty
    if (current_time + timedelta(minutes=travel_distances["Bayview"]["Haight-Ashbury"])).time() < betty_start_time.time():
        current_time += timedelta(minutes=travel_distances["Bayview"]["Haight-Ashbury"])
        schedule.append({
            "action": "meet",
            "location": "Haight-Ashbury",
            "person": "Betty",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Betty"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Betty"]
        current_time += compute_travel_time("Haight-Ashbury", "Bayview")
        current_time = start_time
    else:
        current_time += timedelta(minutes=travel_distances["Bayview"]["Haight-Ashbury"])
        schedule.append({
            "action": "meet",
            "location": "Haight-Ashbury",
            "person": "Betty",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Betty"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Betty"]
        current_time += compute_travel_time("Haight-Ashbury", "Bayview")
        current_time = start_time

    # Meet Charles
    if (current_time + timedelta(minutes=travel_distances["Bayview"]["Financial District"])).time() < charles_start_time.time():
        current_time += timedelta(minutes=travel_distances["Bayview"]["Financial District"])
        schedule.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Charles",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Charles"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Charles"]
        current_time += compute_travel_time("Financial District", "Bayview")
        current_time = start_time
    else:
        current_time += timedelta(minutes=travel_distances["Bayview"]["Financial District"])
        schedule.append({
            "action": "meet",
            "location": "Financial District",
            "person": "Charles",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Charles"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Charles"]
        current_time += compute_travel_time("Financial District", "Bayview")
        current_time = start_time

    # Meet Mary
    if (current_time + timedelta(minutes=travel_distances["Bayview"]["Pacific Heights"])).time() < mary_start_time.time():
        current_time += timedelta(minutes=travel_distances["Bayview"]["Pacific Heights"])
        schedule.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Mary",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Mary"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Mary"]
        current_time += compute_travel_time("Pacific Heights", "Bayview")
        current_time = start_time
    else:
        current_time += timedelta(minutes=travel_distances["Bayview"]["Pacific Heights"])
        schedule.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Mary",
            "start_time": current_time.strftime("%H:%M"),
            "end_time": (current_time + min_meeting_times["Mary"]).strftime("%H:%M")
        })
        current_time += min_meeting_times["Mary"]
        current_time += compute_travel_time("Pacific Heights", "Bayview")
        current_time = start_time

    # Meet Lisa
    current_time = lisa_start_time
    schedule.append({
        "action": "meet",
        "location": meeting_locations["Lisa"],
        "person": "Lisa",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": (current_time + min_meeting_times["Lisa"]).strftime("%H:%M")
    })
    current_time += min_meeting_times["Lisa"]

    return schedule

def main():
    schedule = compute_meeting_schedule()
    print(json.dumps({"itinerary": schedule}, indent=4))

if __name__ == "__main__":
    main()