import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
}

# Meeting windows and minimum durations
meetings = {
    "Sarah": {"location": "North Beach", "available": (16 * 60, 18 * 60 + 15), "min_duration": 60},
    "Jeffrey": {"location": "Union Square", "available": (15 * 60, 22 * 60), "min_duration": 75},
    "Brian": {"location": "Alamo Square", "available": (16 * 60, 17 * 60 + 30), "min_duration": 75}
}

# Starting time
start_time = 9 * 60  # 9:00 AM in minutes
end_time = 22 * 60   # 10:00 PM in minutes

# Function to add time in minutes to a time
def add_time(base_time, minutes):
    return base_time + minutes

# Function to convert minutes to HH:MM format
def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02}"

# Function to calculate the optimal meeting schedule
def calculate_schedule(travel_times, meetings, start_time):
    schedule = []
    current_time = start_time
    
    # Meeting Sarah
    if current_time <= meetings["Sarah"]["available"][1]:
        travel_time = travel_times[("Sunset District", "North Beach")]
        available_start = max(meetings["Sarah"]["available"][0], current_time + travel_time)
        meeting_end = available_start + meetings["Sarah"]["min_duration"]
        
        if meeting_end <= meetings["Sarah"]["available"][1]:
            schedule.append({
                "action": "meet",
                "location": meetings["Sarah"]["location"],
                "person": "Sarah",
                "start_time": minutes_to_time(available_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end + travel_times[("North Beach", "Union Square")]
    
    # Meeting Jeffrey
    if current_time <= meetings["Jeffrey"]["available"][1]:
        travel_time = travel_times[("Sunset District", "Union Square")]
        available_start = max(meetings["Jeffrey"]["available"][0], current_time)
        meeting_end = available_start + meetings["Jeffrey"]["min_duration"]
        
        if meeting_end <= meetings["Jeffrey"]["available"][1]:
            schedule.append({
                "action": "meet",
                "location": meetings["Jeffrey"]["location"],
                "person": "Jeffrey",
                "start_time": minutes_to_time(available_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end

    # Meeting Brian
    if current_time <= meetings["Brian"]["available"][1]:
        travel_time = travel_times[("Union Square", "Alamo Square")]
        available_start = max(meetings["Brian"]["available"][0], current_time)
        meeting_end = available_start + meetings["Brian"]["min_duration"]
        
        if meeting_end <= meetings["Brian"]["available"][1]:
            schedule.append({
                "action": "meet",
                "location": meetings["Brian"]["location"],
                "person": "Brian",
                "start_time": minutes_to_time(available_start),
                "end_time": minutes_to_time(meeting_end)
            })

    return {"itinerary": schedule}

# Calculate the schedule
optimal_schedule = calculate_schedule(travel_times, meetings, start_time)

# Output the result as JSON
print(json.dumps(optimal_schedule, indent=2))