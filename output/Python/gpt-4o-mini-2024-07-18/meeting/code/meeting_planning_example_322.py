import json
from datetime import datetime, timedelta

# Define meeting locations and travel times
travel_times = {
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Presidio"): 17,
}

# Define participants with their availability and required meeting time
participants = {
    "William": {"location": "Russian Hill", "available": (datetime.strptime("18:30", "%H:%M"), datetime.strptime("20:45", "%H:%M")), "min_meeting_time": timedelta(minutes=105)},
    "Michelle": {"location": "Chinatown", "available": (datetime.strptime("08:15", "%H:%M"), datetime.strptime("14:00", "%H:%M")), "min_meeting_time": timedelta(minutes=15)},
    "George": {"location": "Presidio", "available": (datetime.strptime("10:30", "%H:%M"), datetime.strptime("18:45", "%H:%M")), "min_meeting_time": timedelta(minutes=30)},
    "Robert": {"location": "Fisherman's Wharf", "available": (datetime.strptime("09:00", "%H:%M"), datetime.strptime("13:45", "%H:%M")), "min_meeting_time": timedelta(minutes=30)},
}

start_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Create a method to calculate meeting time slots
def can_meet(person, start_time, duration):
    end_time = start_time + duration
    av_start, av_end = participants[person]["available"]
    return start_time >= av_start and end_time <= av_end

# Function to compute the meeting schedule
def schedule_meetings(start_time, current_location):
    meetings = []

    # Try to meet each participant in order of priority
    if can_meet("Robert", start_time + timedelta(minutes=travel_times[(current_location, "Fisherman's Wharf")]), participants["Robert"]["min_meeting_time"]):
        meet_start = start_time + timedelta(minutes=travel_times[(current_location, "Fisherman's Wharf")])
        meetings.append({
            "action": "meet",
            "location": "Fisherman's Wharf",
            "person": "Robert",
            "start_time": meet_start.strftime("%H:%M"),
            "end_time": (meet_start + participants["Robert"]["min_meeting_time"]).strftime("%H:%M"),
        })
        start_time = meet_start + participants["Robert"]["min_meeting_time"]

    if can_meet("Michelle", start_time + timedelta(minutes=travel_times[(current_location, "Chinatown")]), participants["Michelle"]["min_meeting_time"]):
        meet_start = start_time + timedelta(minutes=travel_times[(current_location, "Chinatown")])
        meetings.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Michelle",
            "start_time": meet_start.strftime("%H:%M"),
            "end_time": (meet_start + participants["Michelle"]["min_meeting_time"]).strftime("%H:%M"),
        })
        start_time = meet_start + participants["Michelle"]["min_meeting_time"]

    if can_meet("George", start_time + timedelta(minutes=travel_times[(current_location, "Presidio")]), participants["George"]["min_meeting_time"]):
        meet_start = start_time + timedelta(minutes=travel_times[(current_location, "Presidio")])
        meetings.append({
            "action": "meet",
            "location": "Presidio",
            "person": "George",
            "start_time": meet_start.strftime("%H:%M"),
            "end_time": (meet_start + participants["George"]["min_meeting_time"]).strftime("%H:%M"),
        })
        start_time = meet_start + participants["George"]["min_meeting_time"]

    if can_meet("William", start_time + timedelta(minutes=travel_times[(current_location, "Russian Hill")]), participants["William"]["min_meeting_time"]):
        meet_start = start_time + timedelta(minutes=travel_times[(current_location, "Russian Hill")])
        meetings.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "William",
            "start_time": meet_start.strftime("%H:%M"),
            "end_time": (meet_start + participants["William"]["min_meeting_time"]).strftime("%H:%M"),
        })

    return meetings

# Compute the optimal schedule starting from Sunset District
itinerary = schedule_meetings(start_time, "Sunset District")

# Output in JSON format
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))