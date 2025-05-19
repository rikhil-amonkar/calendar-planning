import json
from datetime import datetime, timedelta

# Define travel distances
travel_times = {
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Bayview"): 23,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 22,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 26,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Golden Gate Park", "Bayview"): 22,
}

# Meeting constraints
constraints = {
    "Matthew": {"location": "Presidio", "start": "11:00", "end": "21:00", "duration": 90},
    "Margaret": {"location": "Chinatown", "start": "09:15", "end": "18:45", "duration": 90},
    "Nancy": {"location": "Pacific Heights", "start": "14:15", "end": "17:00", "duration": 15},
    "Helen": {"location": "Richmond District", "start": "19:45", "end": "22:00", "duration": 60},
    "Rebecca": {"location": "Fisherman's Wharf", "start": "21:15", "end": "22:15", "duration": 60},
    "Kimberly": {"location": "Golden Gate Park", "start": "13:00", "end": "16:30", "duration": 120},
    "Kenneth": {"location": "Bayview", "start": "14:30", "end": "18:00", "duration": 60},
}

# Convert time string to datetime object
def str_to_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Create a function to compute the optimal meeting schedule
def compute_schedule():
    current_time = str_to_time("9:00")
    schedule = []
    
    # Meet Margaret first
    margaret_start = str_to_time("9:15")
    travel_to_margaret = travel_times[("Russian Hill", "Chinatown")]
    time_after_travel = current_time + timedelta(minutes=travel_to_margaret)

    if time_after_travel <= margaret_start:
        free_time = margaret_start - time_after_travel
        if free_time.total_seconds() >= 0:
            actual_start = margaret_start
        else:
            actual_start = time_after_travel

        meet_duration = timedelta(minutes=constraints["Margaret"]["duration"])
        actual_end = actual_start + meet_duration

        schedule.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Margaret",
            "start_time": actual_start.strftime("%H:%M"),
            "end_time": actual_end.strftime("%H:%M")
        })

        # Update current time after meeting Margaret
        current_time = actual_end

    # Meet Matthew next
    travel_to_matthew = travel_times[("Chinatown", "Presidio")]
    time_after_travel = current_time + timedelta(minutes=travel_to_matthew)
    matthew_start = str_to_time("11:00")
    if time_after_travel < matthew_start:
        current_time = matthew_start

    meet_duration = timedelta(minutes=constraints["Matthew"]["duration"])
    actual_end = current_time + meet_duration

    schedule.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Matthew",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": actual_end.strftime("%H:%M")
    })

    current_time = actual_end

    # Meet Kimberly next
    travel_to_kimberly = travel_times[("Presidio", "Golden Gate Park")]
    time_after_travel = current_time + timedelta(minutes=travel_to_kimberly)
    kimberly_start = str_to_time("13:00")
    if time_after_travel < kimberly_start:
        current_time = kimberly_start

    meet_duration = timedelta(minutes=constraints["Kimberly"]["duration"])
    actual_end = current_time + meet_duration

    schedule.append({
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Kimberly",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": actual_end.strftime("%H:%M")
    })

    current_time = actual_end

    # Meet Kenneth next
    travel_to_kenneth = travel_times[("Golden Gate Park", "Bayview")]
    time_after_travel = current_time + timedelta(minutes=travel_to_kenneth)
    kenneth_start = str_to_time("14:30")
    if time_after_travel < kenneth_start:
        current_time = kenneth_start

    meet_duration = timedelta(minutes=constraints["Kenneth"]["duration"])
    actual_end = current_time + meet_duration

    schedule.append({
        "action": "meet",
        "location": "Bayview",
        "person": "Kenneth",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": actual_end.strftime("%H:%M")
    })

    current_time = actual_end

    # Meet Nancy next
    travel_to_nancy = travel_times[("Bayview", "Pacific Heights")]
    time_after_travel = current_time + timedelta(minutes=travel_to_nancy)
    nancy_start = str_to_time("14:15")
    if time_after_travel < nancy_start:
        current_time = nancy_start

    meet_duration = timedelta(minutes=constraints["Nancy"]["duration"])
    actual_end = current_time + meet_duration

    schedule.append({
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Nancy",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": actual_end.strftime("%H:%M")
    })

    current_time = actual_end

    # Meet Helen next
    travel_to_helen = travel_times[("Pacific Heights", "Richmond District")]
    time_after_travel = current_time + timedelta(minutes=travel_to_helen)
    helen_start = str_to_time("19:45")
    if time_after_travel < helen_start:
        current_time = helen_start

    meet_duration = timedelta(minutes=constraints["Helen"]["duration"])
    actual_end = current_time + meet_duration

    schedule.append({
        "action": "meet",
        "location": "Richmond District",
        "person": "Helen",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": actual_end.strftime("%H:%M")
    })

    current_time = actual_end

    # Meet Rebecca last
    travel_to_rebecca = travel_times[("Richmond District", "Fisherman's Wharf")]
    time_after_travel = current_time + timedelta(minutes=travel_to_rebecca)
    rebecca_start = str_to_time("21:15")
    if time_after_travel < rebecca_start:
        current_time = rebecca_start

    meet_duration = timedelta(minutes=constraints["Rebecca"]["duration"])
    actual_end = current_time + meet_duration

    schedule.append({
        "action": "meet",
        "location": "Fisherman's Wharf",
        "person": "Rebecca",
        "start_time": current_time.strftime("%H:%M"),
        "end_time": actual_end.strftime("%H:%M")
    })

    return {"itinerary": schedule}

# Generate the schedule and output as JSON
optimal_schedule = compute_schedule()
print(json.dumps(optimal_schedule, indent=2))