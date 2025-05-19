import json
from datetime import datetime, timedelta

# Defining travel times in minutes
travel_times = {
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Bayview"): 22,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Fisherman's Wharf"): 25,
}

# Defining meeting constraints
constraints = {
    "Helen": {
        "location": "North Beach",
        "start_time": "7:00",
        "end_time": "16:45",
        "duration": 120
    },
    "Kimberly": {
        "location": "Fisherman's Wharf",
        "start_time": "16:30",
        "end_time": "21:00",
        "duration": 45
    },
    "Patricia": {
        "location": "Bayview",
        "start_time": "18:00",
        "end_time": "21:15",
        "duration": 120
    },
}

# Start time at Nob Hill
arrival_time_nob_hill = datetime.strptime("9:00", "%H:%M")

# Calculating the optimal schedule
def calculate_schedule():
    schedule = []
    
    # Meeting Helen
    start_meeting_helen = arrival_time_nob_hill + timedelta(minutes=travel_times[("Nob Hill", "North Beach")])
    end_meeting_helen = start_meeting_helen + timedelta(minutes=constraints["Helen"]["duration"])

    if start_meeting_helen.time() >= datetime.strptime(constraints["Helen"]["start_time"], "%H:%M").time() and \
       end_meeting_helen.time() <= datetime.strptime(constraints["Helen"]["end_time"], "%H:%M").time():
        schedule.append({
            "action": "meet",
            "location": constraints["Helen"]["location"],
            "person": "Helen",
            "start_time": start_meeting_helen.strftime("%H:%M"),
            "end_time": end_meeting_helen.strftime("%H:%M"),
        })
        
        # Travel to Fisherman's Wharf to meet Kimberly after meeting Helen
        travel_to_kimberly = travel_times[("North Beach", "Fisherman's Wharf")]
        start_meeting_kimberly = end_meeting_helen + timedelta(minutes=travel_to_kimberly)
        end_meeting_kimberly = start_meeting_kimberly + timedelta(minutes=constraints["Kimberly"]["duration"])

        if start_meeting_kimberly.time() >= datetime.strptime(constraints["Kimberly"]["start_time"], "%H:%M").time() and \
           end_meeting_kimberly.time() <= datetime.strptime(constraints["Kimberly"]["end_time"], "%H:%M").time():
            schedule.append({
                "action": "meet",
                "location": constraints["Kimberly"]["location"],
                "person": "Kimberly",
                "start_time": start_meeting_kimberly.strftime("%H:%M"),
                "end_time": end_meeting_kimberly.strftime("%H:%M"),
            })

            # Travel to Bayview to meet Patricia after meeting Kimberly
            travel_to_patricia = travel_times[("Fisherman's Wharf", "Bayview")]
            start_meeting_patricia = end_meeting_kimberly + timedelta(minutes=travel_to_patricia)
            end_meeting_patricia = start_meeting_patricia + timedelta(minutes=constraints["Patricia"]["duration"])

            if start_meeting_patricia.time() >= datetime.strptime(constraints["Patricia"]["start_time"], "%H:%M").time() and \
               end_meeting_patricia.time() <= datetime.strptime(constraints["Patricia"]["end_time"], "%H:%M").time():
                schedule.append({
                    "action": "meet",
                    "location": constraints["Patricia"]["location"],
                    "person": "Patricia",
                    "start_time": start_meeting_patricia.strftime("%H:%M"),
                    "end_time": end_meeting_patricia.strftime("%H:%M"),
                })

    return schedule

# Create the itinerary
itinerary = calculate_schedule()

# Format into JSON output
output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))