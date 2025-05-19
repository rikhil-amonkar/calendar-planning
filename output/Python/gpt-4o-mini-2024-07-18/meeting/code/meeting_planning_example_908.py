import json
from datetime import datetime, timedelta

# Meeting parameters
travel_times = {
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Sunset District"): 17,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Sunset District"): 27,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Union Square"): 30,
}

meetings_constraints = {
    "Mark": {"location": "Fisherman's Wharf", "start": "08:15", "end": "10:00", "duration": 30},
    "Stephanie": {"location": "Presidio", "start": "12:15", "end": "15:00", "duration": 75},
    "Betty": {"location": "Bayview", "start": "07:15", "end": "20:30", "duration": 15},
    "Lisa": {"location": "Haight-Ashbury", "start": "15:30", "end": "18:30", "duration": 45},
    "William": {"location": "Russian Hill", "start": "18:45", "end": "20:00", "duration": 60},
    "Brian": {"location": "The Castro", "start": "09:15", "end": "13:15", "duration": 30},
    "Joseph": {"location": "Marina District", "start": "10:45", "end": "15:00", "duration": 90},
    "Ashley": {"location": "Richmond District", "start": "09:45", "end": "11:15", "duration": 45},
    "Patricia": {"location": "Union Square", "start": "16:30", "end": "20:00", "duration": 120},
    "Karen": {"location": "Sunset District", "start": "16:30", "end": "22:00", "duration": 105},
}

# Initial parameters
start_time = datetime.strptime("09:00", "%H:%M")
itinerary = []

# Function to add meeting to itinerary
def add_meeting(person, location, start, end):
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": start.strftime("%H:%M"),
        "end_time": end.strftime("%H:%M")
    })

def schedule_meetings():
    current_time = start_time

    # Meeting Mark
    mark_end = datetime.strptime(meetings_constraints["Mark"]["end"], "%H:%M")
    mark_duration = timedelta(minutes=meetings_constraints["Mark"]["duration"])
    mark_meeting_start = max(current_time, datetime.strptime(meetings_constraints["Mark"]["start"], "%H:%M"))
    mark_meeting_end = mark_meeting_start + mark_duration

    if mark_meeting_end <= mark_end:
        add_meeting("Mark", "Fisherman's Wharf", mark_meeting_start, mark_meeting_end)
        travel_time = travel_times[("Financial District", "Fisherman's Wharf")]
        current_time = mark_meeting_end + timedelta(minutes=travel_time)

    # Meeting Brian
    brian_end = datetime.strptime(meetings_constraints["Brian"]["end"], "%H:%M")
    brian_duration = timedelta(minutes=meetings_constraints["Brian"]["duration"])
    brian_meeting_start = max(current_time, datetime.strptime(meetings_constraints["Brian"]["start"], "%H:%M"))
    brian_meeting_end = brian_meeting_start + brian_duration

    if brian_meeting_end <= brian_end:
        add_meeting("Brian", "The Castro", brian_meeting_start, brian_meeting_end)
        travel_time = travel_times[("Fisherman's Wharf", "The Castro")]
        current_time = brian_meeting_end + timedelta(minutes=travel_time)

    # Meeting Joseph
    joseph_end = datetime.strptime(meetings_constraints["Joseph"]["end"], "%H:%M")
    joseph_duration = timedelta(minutes=meetings_constraints["Joseph"]["duration"])
    joseph_meeting_start = max(current_time, datetime.strptime(meetings_constraints["Joseph"]["start"], "%H:%M"))
    joseph_meeting_end = joseph_meeting_start + joseph_duration

    if joseph_meeting_end <= joseph_end:
        add_meeting("Joseph", "Marina District", joseph_meeting_start, joseph_meeting_end)
        travel_time = travel_times[("The Castro", "Marina District")]
        current_time = joseph_meeting_end + timedelta(minutes=travel_time)

    # Meeting Ashley
    ashley_end = datetime.strptime(meetings_constraints["Ashley"]["end"], "%H:%M")
    ashley_duration = timedelta(minutes=meetings_constraints["Ashley"]["duration"])
    ashley_meeting_start = max(current_time, datetime.strptime(meetings_constraints["Ashley"]["start"], "%H:%M"))
    ashley_meeting_end = ashley_meeting_start + ashley_duration

    if ashley_meeting_end <= ashley_end:
        add_meeting("Ashley", "Richmond District", ashley_meeting_start, ashley_meeting_end)
        travel_time = travel_times[("Marina District", "Richmond District")]
        current_time = ashley_meeting_end + timedelta(minutes=travel_time)

    # Meeting Stephanie
    stephanie_end = datetime.strptime(meetings_constraints["Stephanie"]["end"], "%H:%M")
    stephanie_duration = timedelta(minutes=meetings_constraints["Stephanie"]["duration"])
    stephanie_meeting_start = max(current_time, datetime.strptime(meetings_constraints["Stephanie"]["start"], "%H:%M"))
    stephanie_meeting_end = stephanie_meeting_start + stephanie_duration

    if stephanie_meeting_end <= stephanie_end:
        add_meeting("Stephanie", "Presidio", stephanie_meeting_start, stephanie_meeting_end)
        travel_time = travel_times[("Richmond District", "Presidio")]
        current_time = stephanie_meeting_end + timedelta(minutes=travel_time)

    # Meeting Lisa
    lisa_end = datetime.strptime(meetings_constraints["Lisa"]["end"], "%H:%M")
    lisa_duration = timedelta(minutes=meetings_constraints["Lisa"]["duration"])
    lisa_meeting_start = max(current_time, datetime.strptime(meetings_constraints["Lisa"]["start"], "%H:%M"))
    lisa_meeting_end = lisa_meeting_start + lisa_duration

    if lisa_meeting_end <= lisa_end:
        add_meeting("Lisa", "Haight-Ashbury", lisa_meeting_start, lisa_meeting_end)
        travel_time = travel_times[("Presidio", "Haight-Ashbury")]
        current_time = lisa_meeting_end + timedelta(minutes=travel_time)

    # Meeting William
    william_end = datetime.strptime(meetings_constraints["William"]["end"], "%H:%M")
    william_duration = timedelta(minutes=meetings_constraints["William"]["duration"])
    william_meeting_start = max(current_time, datetime.strptime(meetings_constraints["William"]["start"], "%H:%M"))
    william_meeting_end = william_meeting_start + william_duration

    if william_meeting_end <= william_end:
        add_meeting("William", "Russian Hill", william_meeting_start, william_meeting_end)
        travel_time = travel_times[("Haight-Ashbury", "Russian Hill")]
        current_time = william_meeting_end + timedelta(minutes=travel_time)

    # Meeting Patricia
    patricia_end = datetime.strptime(meetings_constraints["Patricia"]["end"], "%H:%M")
    patricia_duration = timedelta(minutes=meetings_constraints["Patricia"]["duration"])
    patricia_meeting_start = max(current_time, datetime.strptime(meetings_constraints["Patricia"]["start"], "%H:%M"))
    patricia_meeting_end = patricia_meeting_start + patricia_duration

    if patricia_meeting_end <= patricia_end:
        add_meeting("Patricia", "Union Square", patricia_meeting_start, patricia_meeting_end)
        travel_time = travel_times[("Russian Hill", "Union Square")]
        current_time = patricia_meeting_end + timedelta(minutes=travel_time)

    # Meeting Karen
    karen_end = datetime.strptime(meetings_constraints["Karen"]["end"], "%H:%M")
    karen_duration = timedelta(minutes=meetings_constraints["Karen"]["duration"])
    karen_meeting_start = max(current_time, datetime.strptime(meetings_constraints["Karen"]["start"], "%H:%M"))
    karen_meeting_end = karen_meeting_start + karen_duration

    if karen_meeting_end <= karen_end:
        add_meeting("Karen", "Sunset District", karen_meeting_start, karen_meeting_end)

# Schedule all meetings based on constraints
schedule_meetings()

# Format result to JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))