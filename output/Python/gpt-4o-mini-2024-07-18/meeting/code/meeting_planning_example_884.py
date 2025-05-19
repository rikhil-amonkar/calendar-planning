from datetime import datetime, timedelta
import json

# Define travel times (in minutes)
travel_times = {
    "Richmond District": {
        "Chinatown": 20,
        "Sunset District": 11,
        "Alamo Square": 13,
        "Financial District": 22,
        "North Beach": 17,
        "Embarcadero": 19,
        "Presidio": 7,
        "Golden Gate Park": 9,
        "Bayview": 27
    },
    "Chinatown": {
        "Richmond District": 20,
        "Sunset District": 29,
        "Alamo Square": 17,
        "Financial District": 5,
        "North Beach": 3,
        "Embarcadero": 5,
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 20
    },
    "Sunset District": {
        "Richmond District": 12,
        "Chinatown": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "North Beach": 28,
        "Embarcadero": 30,
        "Presidio": 16,
        "Golden Gate Park": 11,
        "Bayview": 22
    },
    "Alamo Square": {
        "Richmond District": 11,
        "Chinatown": 15,
        "Sunset District": 16,
        "Financial District": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Presidio": 17,
        "Golden Gate Park": 9,
        "Bayview": 16
    },
    "Financial District": {
        "Richmond District": 21,
        "Chinatown": 5,
        "Sunset District": 30,
        "Alamo Square": 17,
        "North Beach": 7,
        "Embarcadero": 4,
        "Presidio": 22,
        "Golden Gate Park": 23,
        "Bayview": 19
    },
    "North Beach": {
        "Richmond District": 18,
        "Chinatown": 6,
        "Sunset District": 27,
        "Alamo Square": 16,
        "Financial District": 8,
        "Embarcadero": 6,
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 25
    },
    "Embarcadero": {
        "Richmond District": 21,
        "Chinatown": 7,
        "Sunset District": 30,
        "Alamo Square": 19,
        "Financial District": 5,
        "North Beach": 5,
        "Presidio": 20,
        "Golden Gate Park": 25,
        "Bayview": 21
    },
    "Presidio": {
        "Richmond District": 7,
        "Chinatown": 21,
        "Sunset District": 15,
        "Alamo Square": 19,
        "Financial District": 23,
        "North Beach": 18,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Bayview": 31
    },
    "Golden Gate Park": {
        "Richmond District": 7,
        "Chinatown": 23,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "North Beach": 23,
        "Embarcadero": 25,
        "Presidio": 11,
        "Bayview": 23
    },
    "Bayview": {
        "Richmond District": 25,
        "Chinatown": 19,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "North Beach": 22,
        "Embarcadero": 19,
        "Presidio": 32,
        "Golden Gate Park": 22
    }
}

# Define meeting constraints
meetings = [
    {"person": "Robert", "location": "Chinatown", "start_time": "7:45", "end_time": "17:30", "duration": 120},
    {"person": "David", "location": "Sunset District", "start_time": "12:30", "end_time": "19:45", "duration": 45},
    {"person": "Matthew", "location": "Alamo Square", "start_time": "8:45", "end_time": "13:45", "duration": 90},
    {"person": "Jessica", "location": "Financial District", "start_time": "9:30", "end_time": "18:45", "duration": 45},
    {"person": "Melissa", "location": "North Beach", "start_time": "7:15", "end_time": "16:45", "duration": 45},
    {"person": "Mark", "location": "Embarcadero", "start_time": "15:15", "end_time": "17:00", "duration": 45},
    {"person": "Deborah", "location": "Presidio", "start_time": "19:00", "end_time": "19:45", "duration": 45},
    {"person": "Karen", "location": "Golden Gate Park", "start_time": "19:30", "end_time": "22:00", "duration": 120},
    {"person": "Laura", "location": "Bayview", "start_time": "21:15", "end_time": "22:15", "duration": 15}
]

# Function to calculate the optimal meeting schedule
def calculate_schedule():
    current_time = datetime.strptime("9:00", "%H:%M")
    schedule = []
    
    # Meeting with Robert
    robert_start = max(current_time, datetime.strptime(meetings[0]["start_time"], "%H:%M"))
    robert_end = robert_start + timedelta(minutes=meetings[0]["duration"])
    travel_to_robert = travel_times["Richmond District"][meetings[0]["location"]]
    
    if robert_end <= datetime.strptime(meetings[0]["end_time"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": meetings[0]["location"],
            "person": meetings[0]["person"],
            "start_time": robert_start.strftime("%H:%M"),
            "end_time": robert_end.strftime("%H:%M")
        })
        current_time = robert_end + timedelta(minutes=travel_to_robert)

    # Next, meet Matthew
    matthew_start = max(current_time, datetime.strptime(meetings[2]["start_time"], "%H:%M"))
    matthew_end = matthew_start + timedelta(minutes=meetings[2]["duration"])
    travel_to_matthew = travel_times["Richmond District"][meetings[2]["location"]]

    if matthew_end <= datetime.strptime(meetings[2]["end_time"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": meetings[2]["location"],
            "person": meetings[2]["person"],
            "start_time": matthew_start.strftime("%H:%M"),
            "end_time": matthew_end.strftime("%H:%M")
        })
        current_time = matthew_end + timedelta(minutes=travel_to_matthew)

    # Meeting with Jessica
    jessica_start = max(current_time, datetime.strptime(meetings[3]["start_time"], "%H:%M"))
    jessica_end = jessica_start + timedelta(minutes=meetings[3]["duration"])
    travel_to_jessica = travel_times["Richmond District"][meetings[3]["location"]]

    if jessica_end <= datetime.strptime(meetings[3]["end_time"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": meetings[3]["location"],
            "person": meetings[3]["person"],
            "start_time": jessica_start.strftime("%H:%M"),
            "end_time": jessica_end.strftime("%H:%M")
        })
        current_time = jessica_end + timedelta(minutes=travel_to_jessica)

    # Meeting with David
    david_start = max(current_time, datetime.strptime(meetings[1]["start_time"], "%H:%M"))
    david_end = david_start + timedelta(minutes=meetings[1]["duration"])
    travel_to_david = travel_times[meetings[3]["location"]][meetings[1]["location"]]

    # Check if David's meeting can be accommodated
    if david_end <= datetime.strptime(meetings[1]["end_time"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": meetings[1]["location"],
            "person": meetings[1]["person"],
            "start_time": david_start.strftime("%H:%M"),
            "end_time": david_end.strftime("%H:%M")
        })
        current_time = david_end + timedelta(minutes=travel_to_david)

    # Meeting with Mark
    mark_start = max(current_time, datetime.strptime(meetings[5]["start_time"], "%H:%M"))
    mark_end = mark_start + timedelta(minutes=meetings[5]["duration"])
    travel_to_mark = travel_times[meetings[1]["location"]][meetings[5]["location"]]

    if mark_end <= datetime.strptime(meetings[5]["end_time"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": meetings[5]["location"],
            "person": meetings[5]["person"],
            "start_time": mark_start.strftime("%H:%M"),
            "end_time": mark_end.strftime("%H:%M")
        })
        current_time = mark_end + timedelta(minutes=travel_to_mark)

    # Meeting with Deborah
    deborah_start = max(current_time, datetime.strptime(meetings[6]["start_time"], "%H:%M"))
    deborah_end = deborah_start + timedelta(minutes=meetings[6]["duration"])
    travel_to_deborah = travel_times[meetings[5]["location"]][meetings[6]["location"]]

    if deborah_start <= datetime.strptime(meetings[6]["end_time"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": meetings[6]["location"],
            "person": meetings[6]["person"],
            "start_time": deborah_start.strftime("%H:%M"),
            "end_time": deborah_end.strftime("%H:%M")
        })
        current_time = deborah_end + timedelta(minutes=travel_to_deborah)

    # Meeting with Karen
    karen_start = max(current_time, datetime.strptime(meetings[7]["start_time"], "%H:%M"))
    karen_end = karen_start + timedelta(minutes=meetings[7]["duration"])
    travel_to_karen = travel_times[meetings[6]["location"]][meetings[7]["location"]]

    if karen_end <= datetime.strptime(meetings[7]["end_time"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": meetings[7]["location"],
            "person": meetings[7]["person"],
            "start_time": karen_start.strftime("%H:%M"),
            "end_time": karen_end.strftime("%H:%M")
        })
        current_time = karen_end + timedelta(minutes=travel_to_karen)

    # Meeting with Laura
    laura_start = max(current_time, datetime.strptime(meetings[8]["start_time"], "%H:%M"))
    laura_end = laura_start + timedelta(minutes=meetings[8]["duration"])
    travel_to_laura = travel_times[meetings[7]["location"]][meetings[8]["location"]]

    if laura_end <= datetime.strptime(meetings[8]["end_time"], "%H:%M"):
        schedule.append({
            "action": "meet",
            "location": meetings[8]["location"],
            "person": meetings[8]["person"],
            "start_time": laura_start.strftime("%H:%M"),
            "end_time": laura_end.strftime("%H:%M")
        })

    return {"itinerary": schedule}

# Calculate the schedule
optimal_schedule = calculate_schedule()

# Output the schedule as JSON
print(json.dumps(optimal_schedule, indent=2))