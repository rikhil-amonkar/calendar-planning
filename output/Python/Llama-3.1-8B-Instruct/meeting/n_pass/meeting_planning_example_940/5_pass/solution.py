import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    "Union Square": {
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Russian Hill": 13,
        "Marina District": 18,
        "North Beach": 10,
        "Chinatown": 7,
        "Pacific Heights": 15,
        "The Castro": 17,
        "Nob Hill": 9,
        "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Russian Hill": 15,
        "Marina District": 19,
        "North Beach": 17,
        "Chinatown": 16,
        "Pacific Heights": 16,
        "The Castro": 7,
        "Nob Hill": 12,
        "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "Mission District": 22,
        "Russian Hill": 7,
        "Marina District": 9,
        "North Beach": 6,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "The Castro": 27,
        "Nob Hill": 11,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Marina District": 7,
        "North Beach": 5,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "The Castro": 21,
        "Nob Hill": 5,
        "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16,
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Pacific Heights": 7,
        "The Castro": 22,
        "Nob Hill": 12,
        "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7,
        "Mission District": 18,
        "Fisherman's Wharf": 5,
        "Russian Hill": 4,
        "Marina District": 9,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 23,
        "Nob Hill": 7,
        "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7,
        "Mission District": 17,
        "Fisherman's Wharf": 8,
        "Russian Hill": 7,
        "Marina District": 12,
        "North Beach": 3,
        "Pacific Heights": 10,
        "The Castro": 22,
        "Nob Hill": 9,
        "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 15,
        "Mission District": 15,
        "Fisherman's Wharf": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "North Beach": 9,
        "Chinatown": 11,
        "The Castro": 16,
        "Nob Hill": 8,
        "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19,
        "Mission District": 7,
        "Fisherman's Wharf": 24,
        "Russian Hill": 18,
        "Marina District": 21,
        "North Beach": 20,
        "Chinatown": 22,
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 9,
        "Mission District": 13,
        "Fisherman's Wharf": 10,
        "Russian Hill": 5,
        "Marina District": 11,
        "North Beach": 8,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 17,
        "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 27,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Russian Hill": 24,
        "Marina District": 21,
        "North Beach": 28,
        "Chinatown": 30,
        "Pacific Heights": 21,
        "The Castro": 17,
        "Nob Hill": 27
    }
}

# Define meeting constraints
meeting_constraints = {
    "Kevin": {"start_time": "20:45", "end_time": "21:45", "duration": 60},
    "Mark": {"start_time": "17:15", "end_time": "20:00", "duration": 90},
    "Jessica": {"start_time": "09:00", "end_time": "15:00", "duration": 120},
    "Jason": {"start_time": "15:15", "end_time": "21:45", "duration": 120},
    "John": {"start_time": "09:45", "end_time": "12:00", "duration": 15},
    "Karen": {"start_time": "16:45", "end_time": "19:00", "duration": 75},
    "Sarah": {"start_time": "17:30", "end_time": "18:15", "duration": 45},
    "Amanda": {"start_time": "20:00", "end_time": "21:15", "duration": 60},
    "Nancy": {"start_time": "09:45", "end_time": "13:00", "duration": 45},
    "Rebecca": {"start_time": "08:45", "end_time": "15:00", "duration": 75}
}

def compute_travel_time(start_location, end_location):
    return travel_distances[start_location][end_location]

def compute_meeting_schedule():
    schedule = []
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("18:00", "%H:%M")

    # Add initial meeting with Kevin
    schedule.append({
        "action": "meet",
        "location": "Mission District",
        "person": "Kevin",
        "start_time": "20:45",
        "end_time": "21:45"
    })

    # Add meeting with Mark
    travel_time = compute_travel_time("Mission District", "Fisherman's Wharf")
    start_time += timedelta(minutes=travel_time + 15)
    schedule.append({
        "action": "meet",
        "location": "Fisherman's Wharf",
        "person": "Mark",
        "start_time": "17:15",
        "end_time": "20:00"
    })

    # Add meeting with Jessica
    travel_time = compute_travel_time("Fisherman's Wharf", "Russian Hill")
    start_time += timedelta(minutes=travel_time + 15)
    jessica_start_time = datetime.strptime(meeting_constraints["Jessica"]["start_time"], "%H:%M")
    jessica_end_time = datetime.strptime(meeting_constraints["Jessica"]["end_time"], "%H:%M")
    if start_time >= jessica_start_time and start_time < jessica_end_time:
        # Jessica is not available at the time of the meeting
        # Add a new meeting with Jessica at a later time
        schedule.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "Jessica",
            "start_time": "15:00",
            "end_time": "15:00"
        })
        start_time += timedelta(minutes=1)
    else:
        schedule.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "Jessica",
            "start_time": "09:00",
            "end_time": "15:00"
        })

    # Add meeting with Jason
    travel_time = compute_travel_time("Russian Hill", "Marina District")
    start_time += timedelta(minutes=travel_time + 15)
    schedule.append({
        "action": "meet",
        "location": "Marina District",
        "person": "Jason",
        "start_time": "15:15",
        "end_time": "21:45"
    })

    # Add meeting with John
    travel_time = compute_travel_time("Marina District", "North Beach")
    john_meeting_end_time = datetime.strptime(meeting_constraints["John"]["end_time"], "%H:%M")
    start_time += timedelta(minutes=travel_time + 15)
    if start_time < john_meeting_end_time:
        # John is not available at the time of the meeting
        # Add a new meeting with John at a later time
        schedule.append({
            "action": "meet",
            "location": "North Beach",
            "person": "John",
            "start_time": "12:00",
            "end_time": "12:00"
        })
    else:
        schedule.append({
            "action": "meet",
            "location": "North Beach",
            "person": "John",
            "start_time": "09:45",
            "end_time": "12:00"
        })

    # Add meeting with Karen
    travel_time = compute_travel_time("North Beach", "Chinatown")
    start_time += timedelta(minutes=travel_time + 15)
    schedule.append({
        "action": "meet",
        "location": "Chinatown",
        "person": "Karen",
        "start_time": "16:45",
        "end_time": "19:00"
    })

    # Add meeting with Sarah
    travel_time = compute_travel_time("Chinatown", "Pacific Heights")
    start_time += timedelta(minutes=travel_time + 15)
    schedule.append({
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Sarah",
        "start_time": "17:30",
        "end_time": "18:15"
    })

    # Add meeting with Amanda
    travel_time = compute_travel_time("Pacific Heights", "The Castro")
    start_time += timedelta(minutes=travel_time + 15)
    schedule.append({
        "action": "meet",
        "location": "The Castro",
        "person": "Amanda",
        "start_time": "20:00",
        "end_time": "21:15"
    })

    # Add meeting with Nancy
    travel_time = compute_travel_time("The Castro", "Nob Hill")
    nancy_start_time = datetime.strptime(meeting_constraints["Nancy"]["start_time"], "%H:%M")
    nancy_end_time = datetime.strptime(meeting_constraints["Nancy"]["end_time"], "%H:%M")
    if start_time >= nancy_start_time and start_time < nancy_end_time:
        # Nancy is not available at the time of the meeting
        # Add a new meeting with Nancy at a later time
        schedule.append({
            "action": "meet",
            "location": "Nob Hill",
            "person": "Nancy",
            "start_time": "13:00",
            "end_time": "13:00"
        })
        start_time += timedelta(minutes=1)
    else:
        schedule.append({
            "action": "meet",
            "location": "Nob Hill",
            "person": "Nancy",
            "start_time": "09:45",
            "end_time": "13:00"
        })

    # Add meeting with Rebecca
    travel_time = compute_travel_time("Nob Hill", "Sunset District")
    end_time_rebecca = datetime.strptime(meeting_constraints["Rebecca"]["end_time"], "%H:%M")
    start_time_rebecca = datetime.strptime(meeting_constraints["Rebecca"]["start_time"], "%H:%M")
    if start_time_rebecca + timedelta(minutes=meeting_constraints["Rebecca"]["duration"]) > end_time_rebecca:
        # Rebecca is already available at the time of the meeting
        start_time += timedelta(minutes=travel_time + 15)
        schedule.append({
            "action": "meet",
            "location": "Sunset District",
            "person": "Rebecca",
            "start_time": "08:45",
            "end_time": "15:00"
        })
    else:
        # Rebecca is not available at the time of the meeting
        # Add a new meeting with Rebecca at a later time
        schedule.append({
            "action": "meet",
            "location": "Sunset District",
            "person": "Rebecca",
            "start_time": "15:00",
            "end_time": "16:15"
        })

    return schedule

def main():
    schedule = compute_meeting_schedule()
    itinerary = []
    for meeting in schedule:
        start_time = datetime.strptime(meeting["start_time"], "%H:%M")
        end_time = datetime.strptime(meeting["end_time"], "%H:%M")
        travel_time = compute_travel_time("Union Square", meeting["location"])
        start_time -= timedelta(minutes=travel_time)
        itinerary.append({
            "action": meeting["action"],
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": start_time.strftime("%H:%M"),
            "end_time": end_time.strftime("%H:%M")
        })
    print(json.dumps({"itinerary": itinerary}, indent=4))

if __name__ == "__main__":
    main()