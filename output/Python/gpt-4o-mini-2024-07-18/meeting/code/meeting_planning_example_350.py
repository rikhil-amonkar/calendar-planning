import json
from datetime import datetime, timedelta

# Define the travel distances in minutes
travel_times = {
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Financial District"): 19,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Financial District"): 13,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Financial District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "Mission District"): 17,
    ("Financial District", "Haight-Ashbury"): 19,
}

# Define meeting constraints
meetings = {
    "Mary": {
        "location": "Pacific Heights",
        "start": datetime.strptime("10:00", "%H:%M"),
        "end": datetime.strptime("19:00", "%H:%M"),
        "duration": timedelta(minutes=45)
    },
    "Lisa": {
        "location": "Mission District",
        "start": datetime.strptime("20:30", "%H:%M"),
        "end": datetime.strptime("22:00", "%H:%M"),
        "duration": timedelta(minutes=75)
    },
    "Betty": {
        "location": "Haight-Ashbury",
        "start": datetime.strptime("07:15", "%H:%M"),
        "end": datetime.strptime("17:15", "%H:%M"),
        "duration": timedelta(minutes=90)
    },
    "Charles": {
        "location": "Financial District",
        "start": datetime.strptime("11:15", "%H:%M"),
        "end": datetime.strptime("15:00", "%H:%M"),
        "duration": timedelta(minutes=120)
    }
}

# Initialize
current_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Function to schedule a meeting
def schedule_meeting(person, meeting_info):
    global current_time
    location = meeting_info["location"]
    meeting_duration = meeting_info["duration"]

    travel_time = travel_times.get(("Bayview", location), None)
    if travel_time is not None:
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can meet
        if arrival_time < meeting_info["start"]:
            start_time = meeting_info["start"]
        else:
            start_time = max(arrival_time, meeting_info["start"])

        end_time = start_time + meeting_duration

        # Check if end time is within the allowable meeting time
        if end_time <= meeting_info["end"]:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": start_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M"),
            })
            current_time = end_time + timedelta(minutes=travel_times.get((location, "Bayview"), 0))

# Schedule meetings one by one
schedule_meeting("Betty", meetings["Betty"])
schedule_meeting("Charles", meetings["Charles"])
schedule_meeting("Mary", meetings["Mary"])
schedule_meeting("Lisa", meetings["Lisa"])

# Output the result as JSON
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))