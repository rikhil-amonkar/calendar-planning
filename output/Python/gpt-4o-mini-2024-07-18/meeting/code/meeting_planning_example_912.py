import json
from datetime import datetime, timedelta

# Dictionary of travel times in minutes
travel_times = {
    "Union Square": {
        "Presidio": 24,
        "Alamo Square": 15,
        "Marina District": 18,
        "Financial District": 9,
        "Nob Hill": 9,
        "Sunset District": 27,
        "Chinatown": 7,
        "Russian Hill": 13,
        "North Beach": 10,
        "Haight-Ashbury": 18,
    },
    "Presidio": {
        "Union Square": 22,
        "Alamo Square": 19,
        "Marina District": 11,
        "Financial District": 23,
        "Nob Hill": 18,
        "Sunset District": 15,
        "Chinatown": 21,
        "Russian Hill": 14,
        "North Beach": 18,
        "Haight-Ashbury": 15,
    },
    "Alamo Square": {
        "Union Square": 14,
        "Presidio": 17,
        "Marina District": 15,
        "Financial District": 17,
        "Nob Hill": 11,
        "Sunset District": 16,
        "Chinatown": 15,
        "Russian Hill": 13,
        "North Beach": 15,
        "Haight-Ashbury": 5,
    },
    "Marina District": {
        "Union Square": 16,
        "Presidio": 10,
        "Alamo Square": 15,
        "Financial District": 17,
        "Nob Hill": 12,
        "Sunset District": 19,
        "Chinatown": 15,
        "Russian Hill": 8,
        "North Beach": 11,
        "Haight-Ashbury": 16,
    },
    "Financial District": {
        "Union Square": 9,
        "Presidio": 22,
        "Alamo Square": 17,
        "Marina District": 15,
        "Nob Hill": 8,
        "Sunset District": 30,
        "Chinatown": 5,
        "Russian Hill": 11,
        "North Beach": 7,
        "Haight-Ashbury": 19,
    },
    "Nob Hill": {
        "Union Square": 7,
        "Presidio": 17,
        "Alamo Square": 11,
        "Marina District": 11,
        "Financial District": 9,
        "Sunset District": 24,
        "Chinatown": 6,
        "Russian Hill": 5,
        "North Beach": 8,
        "Haight-Ashbury": 13,
    },
    "Sunset District": {
        "Union Square": 30,
        "Presidio": 16,
        "Alamo Square": 17,
        "Marina District": 21,
        "Financial District": 30,
        "Nob Hill": 27,
        "Chinatown": 30,
        "Russian Hill": 24,
        "North Beach": 28,
        "Haight-Ashbury": 15,
    },
    "Chinatown": {
        "Union Square": 7,
        "Presidio": 19,
        "Alamo Square": 17,
        "Marina District": 12,
        "Financial District": 5,
        "Nob Hill": 9,
        "Sunset District": 29,
        "Russian Hill": 7,
        "North Beach": 3,
        "Haight-Ashbury": 19,
    },
    "Russian Hill": {
        "Union Square": 10,
        "Presidio": 14,
        "Alamo Square": 15,
        "Marina District": 7,
        "Financial District": 11,
        "Nob Hill": 5,
        "Sunset District": 23,
        "Chinatown": 9,
        "North Beach": 5,
        "Haight-Ashbury": 17,
    },
    "North Beach": {
        "Union Square": 7,
        "Presidio": 17,
        "Alamo Square": 16,
        "Marina District": 9,
        "Financial District": 8,
        "Nob Hill": 7,
        "Sunset District": 27,
        "Chinatown": 6,
        "Russian Hill": 4,
        "Haight-Ashbury": 18,
    },
    "Haight-Ashbury": {
        "Union Square": 19,
        "Presidio": 15,
        "Alamo Square": 5,
        "Marina District": 17,
        "Financial District": 21,
        "Nob Hill": 15,
        "Sunset District": 15,
        "Chinatown": 19,
        "Russian Hill": 17,
        "North Beach": 19,
    },
}

# Meeting constraints
meetings = {
    "Kimberly": ("Presidio", "15:30", "15:45"),  # 15:30 to 16:00
    "Elizabeth": ("Alamo Square", "19:15", "20:15"),  # 19:15 to 20:15
    "Joshua": ("Marina District", "10:30", "14:15"),  # 10:30 to 14:15
    "Sandra": ("Financial District", "19:30", "20:15"),  # 19:30 to 20:15
    "Kenneth": ("Nob Hill", "12:45", "21:45"),  # whole day
    "Betty": ("Sunset District", "14:00", "19:00"),  # 14:00 to 19:00
    "Deborah": ("Chinatown", "17:15", "20:30"),  # 17:15 to 20:30
    "Barbara": ("Russian Hill", "17:30", "21:15"),  # 17:30 to 21:15
    "Steven": ("North Beach", "17:45", "20:45"),  # 17:45 to 20:45
    "Daniel": ("Haight-Ashbury", "18:30", "18:45"),  # 18:30 to 18:45
}

# Define function to compute optimal meeting schedule
def compute_schedule():
    schedule = []
    current_time = datetime.strptime("9:00", "%H:%M")
    
    # Meeting requirements in minutes
    meeting_requirements = {
        "Kimberly": 15,
        "Elizabeth": 15,
        "Joshua": 45,
        "Sandra": 45,
        "Kenneth": 30,
        "Betty": 60,
        "Deborah": 15,
        "Barbara": 120,
        "Steven": 90,
        "Daniel": 15,
    }
    
    # Meeting order based on availability
    meeting_order = [
        ("Joshua", "10:30"), 
        ("Kimberly", "15:30"),
        ("Betty", "14:00"),
        ("Kenneth", "12:45"),
        ("Sandra", "19:30"), 
        ("Elizabeth", "19:15"),
        ("Deborah", "17:15"), 
        ("Barbara", "17:30"), 
        ("Steven", "17:45"),
        ("Daniel", "18:30"),
    ]
    
    for person, available_time in meeting_order:
        location, start_time, end_time = meetings[person]
        start_time_dt = datetime.strptime(start_time, "%H:%M")
        end_time_dt = datetime.strptime(end_time, "%H:%M")
        
        # Calculate travel time to the meeting location
        travel_time = travel_times["Union Square"].get(location, 0)
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        if arrival_time <= start_time_dt:
            # Wait until the meeting can start
            current_time = start_time_dt

        # Check if we can meet for the required time
        meeting_time = meeting_requirements[person]
        meeting_end_time = current_time + timedelta(minutes=meeting_time)

        if meeting_end_time <= end_time_dt:
            # Schedule the meeting
            schedule.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": current_time.strftime("%H:%M"),
                "end_time": meeting_end_time.strftime("%H:%M"),
            })
            # Update current time
            current_time = meeting_end_time
            
            # Update current location to the meeting place
            travel_back_time = travel_times[location]["Union Square"]
            current_time += timedelta(minutes=travel_back_time)
    
    return {"itinerary": schedule}

# Compute the optimal meeting schedule
itinerary = compute_schedule()

# Print the result as JSON
print(json.dumps(itinerary, indent=2))