import json
from datetime import datetime, timedelta

# Define travel times in minutes
travel_times = {
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Financial District"): 19,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Financial District"): 11,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("North Beach", "Bayview"): 22,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
}

# Meeting constraints
constraints = {
    "Joseph": {"location": "Russian Hill", "start": "8:30", "end": "19:15", "duration": 60},
    "Nancy": {"location": "Alamo Square", "start": "11:00", "end": "16:00", "duration": 90},
    "Jason": {"location": "North Beach", "start": "16:45", "end": "21:45", "duration": 15},
    "Jeffrey": {"location": "Financial District", "start": "10:30", "end": "15:45", "duration": 45},
}

# Calculate available time slots given the constraints and travel times
def get_available_times(start_time, end_time, travel_time, duration):
    available_times = []
    current_time = start_time
    while current_time + duration <= end_time:
        available_times.append(current_time)
        current_time += timedelta(minutes=5)  # Check every 5 minutes for a slot
    return available_times

# Schedule meeting considering travel and duration constraints
def schedule_meetings():
    start_day = datetime.strptime("9:00", "%H:%M")  # Starting point in Bayview
    schedule = []

    # Meet Joseph first (must be in Russian Hill)
    joseph_start = datetime.strptime(constraints["Joseph"]["start"], "%H:%M")
    joseph_end = datetime.strptime(constraints["Joseph"]["end"], "%H:%M")
    
    travel_time_to_joseph = travel_times[("Bayview", "Russian Hill")]
    joseph_meeting_times = get_available_times(
        start_day + timedelta(minutes=travel_time_to_joseph),
        joseph_end,
        travel_time_to_joseph,
        timedelta(minutes=constraints["Joseph"]["duration"])
    )
    
    # Pick the first available time to meet Joseph
    if joseph_meeting_times:
        joseph_meeting_time = joseph_meeting_times[0]
        schedule.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "Joseph",
            "start_time": joseph_meeting_time.strftime("%H:%M"),
            "end_time": (joseph_meeting_time + timedelta(minutes=constraints["Joseph"]["duration"])).strftime("%H:%M"),
        })
        
        # After meeting Joseph, head to Jeffrey
        travel_time_to_jeffrey = travel_times[("Russian Hill", "Financial District")]
        travel_time_back_to_bayview = travel_times[("Bayview", "Financial District")]
        
        # Update current time after Joseph meeting
        current_time = joseph_meeting_time + timedelta(minutes=constraints["Joseph"]["duration"] + travel_time_to_jeffrey)
        
        jeffrey_start = datetime.strptime(constraints["Jeffrey"]["start"], "%H:%M")
        jeffrey_end = datetime.strptime(constraints["Jeffrey"]["end"], "%H:%M")
        
        # Ensure meeting Jeffrey is possible
        if current_time < jeffrey_start:
            current_time = jeffrey_start + timedelta(minutes=travel_time_back_to_bayview)

        # Schedule meeting with Jeffrey
        jeffrey_meeting_times = get_available_times(current_time, jeffrey_end, travel_time_back_to_bayview, timedelta(minutes=constraints["Jeffrey"]["duration"]))
        if jeffrey_meeting_times:
            jeffrey_meeting_time = jeffrey_meeting_times[0]
            schedule.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Jeffrey",
                "start_time": jeffrey_meeting_time.strftime("%H:%M"),
                "end_time": (jeffrey_meeting_time + timedelta(minutes=constraints["Jeffrey"]["duration"])).strftime("%H:%M"),
            })
            
            # After meeting Jeffrey, head to Nancy
            travel_time_to_nancy = travel_times[("Financial District", "Alamo Square")]
            current_time = jeffrey_meeting_time + timedelta(minutes=constraints["Jeffrey"]["duration"] + travel_time_to_nancy)
            
            nancy_start = datetime.strptime(constraints["Nancy"]["start"], "%H:%M")
            nancy_end = datetime.strptime(constraints["Nancy"]["end"], "%H:%M")
            
            # Schedule meeting with Nancy
            nancy_meeting_times = get_available_times(current_time, nancy_end, travel_time_to_nancy, timedelta(minutes=constraints["Nancy"]["duration"]))
            if nancy_meeting_times:
                nancy_meeting_time = nancy_meeting_times[0]
                schedule.append({
                    "action": "meet",
                    "location": "Alamo Square",
                    "person": "Nancy",
                    "start_time": nancy_meeting_time.strftime("%H:%M"),
                    "end_time": (nancy_meeting_time + timedelta(minutes=constraints["Nancy"]["duration"])).strftime("%H:%M"),
                })
                
                # Finally, head to Jason
                travel_time_to_jason = travel_times[("Alamo Square", "North Beach")]
                current_time = nancy_meeting_time + timedelta(minutes=constraints["Nancy"]["duration"] + travel_time_to_jason)
                
                jason_start = datetime.strptime(constraints["Jason"]["start"], "%H:%M")
                jason_end = datetime.strptime(constraints["Jason"]["end"], "%H:%M")
                
                # Schedule meeting with Jason
                jason_meeting_times = get_available_times(current_time, jason_end, travel_time_to_jason, timedelta(minutes=constraints["Jason"]["duration"]))
                if jason_meeting_times:
                    jason_meeting_time = jason_meeting_times[0]
                    schedule.append({
                        "action": "meet",
                        "location": "North Beach",
                        "person": "Jason",
                        "start_time": jason_meeting_time.strftime("%H:%M"),
                        "end_time": (jason_meeting_time + timedelta(minutes=constraints["Jason"]["duration"])).strftime("%H:%M"),
                    })

    return {"itinerary": schedule}

# Execute scheduling and print result as JSON
if __name__ == "__main__":
    result = schedule_meetings()
    print(json.dumps(result, indent=2))