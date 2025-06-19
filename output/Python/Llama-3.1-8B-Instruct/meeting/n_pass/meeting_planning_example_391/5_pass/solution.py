import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_distances = {
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Presidio": 16,
        "Financial District": 30
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Russian Hill": 13,
        "Presidio": 18,
        "Financial District": 17
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Alamo Square": 15,
        "Presidio": 14,
        "Financial District": 11
    },
    "Presidio": {
        "Sunset District": 15,
        "Alamo Square": 18,
        "Russian Hill": 14,
        "Financial District": 23
    },
    "Financial District": {
        "Sunset District": 31,
        "Alamo Square": 17,
        "Russian Hill": 10,
        "Presidio": 22
    }
}

# Constraints
start_time = datetime.strptime('09:00', '%H:%M')
kevin_start_time = datetime.strptime('08:15', '%H:%M')
kevin_end_time = datetime.strptime('21:30', '%H:%M')
kimberly_start_time = datetime.strptime('08:45', '%H:%M')
kimberly_end_time = datetime.strptime('12:30', '%H:%M')
joseph_start_time = datetime.strptime('18:30', '%H:%M')
joseph_end_time = datetime.strptime('19:15', '%H:%M')
thomas_start_time = datetime.strptime('19:00', '%H:%M')
thomas_end_time = datetime.strptime('21:45', '%H:%M')
min_meeting_time_kevin = 75
min_meeting_time_kimberly = 30
min_meeting_time_joseph = 45
min_meeting_time_thomas = 45

# Compute optimal meeting schedule
itinerary = []
current_time = start_time

# Meet Kevin
if kimberly_end_time < kevin_start_time:
    # If Kimberly is not available, meet Kevin first
    travel_time = travel_distances["Sunset District"]["Alamo Square"]
    current_time += timedelta(minutes=travel_time)
    itinerary.append({
        "action": "meet",
        "location": "Alamo Square",
        "person": "Kevin",
        "start_time": current_time.strftime('%H:%M'),
        "end_time": (current_time + timedelta(minutes=min_meeting_time_kevin)).strftime('%H:%M')
    })
    current_time += timedelta(minutes=min_meeting_time_kevin)
    travel_time = travel_distances["Alamo Square"]["Sunset District"]
    current_time += timedelta(minutes=travel_time)
else:
    # If Kimberly is available, meet Kimberly first
    travel_time = travel_distances["Sunset District"]["Russian Hill"]
    current_time += timedelta(minutes=travel_time)
    itinerary.append({
        "action": "meet",
        "location": "Russian Hill",
        "person": "Kimberly",
        "start_time": current_time.strftime('%H:%M'),
        "end_time": (current_time + timedelta(minutes=min_meeting_time_kimberly)).strftime('%H:%M')
    })
    current_time += timedelta(minutes=min_meeting_time_kimberly)
    travel_time = travel_distances["Russian Hill"]["Alamo Square"]
    current_time += timedelta(minutes=travel_time)

# Meet Kimberly
travel_time = travel_distances["Alamo Square"]["Russian Hill"]
current_time += timedelta(minutes=travel_time)
itinerary.append({
    "action": "meet",
    "location": "Russian Hill",
    "person": "Kimberly",
    "start_time": current_time.strftime('%H:%M'),
    "end_time": (current_time + timedelta(minutes=min_meeting_time_kimberly)).strftime('%H:%M')
})
current_time += timedelta(minutes=min_meeting_time_kimberly)
travel_time = travel_distances["Russian Hill"]["Sunset District"]
current_time += timedelta(minutes=travel_time)

# Meet Joseph
# Ensure Joseph is available during the meeting time
available_joseph_time = (joseph_start_time + timedelta(minutes=min_meeting_time_joseph))
if current_time < available_joseph_time:
    # If Joseph is available, meet Joseph next
    travel_time = travel_distances["Sunset District"]["Presidio"]
    current_time += timedelta(minutes=travel_time)
    joseph_meeting_start_time = current_time
    joseph_meeting_end_time = joseph_meeting_start_time + timedelta(minutes=min_meeting_time_joseph)
    
    # Ensure Joseph's meeting time is within his available time slot
    if joseph_meeting_start_time < joseph_start_time:
        # If the meeting starts before Joseph's available time, start the meeting at Joseph's available time
        joseph_meeting_start_time = joseph_start_time
        joseph_meeting_end_time = joseph_meeting_start_time + timedelta(minutes=min_meeting_time_joseph)
    elif joseph_meeting_end_time > joseph_end_time:
        # If the meeting ends after Joseph's available time, end the meeting at Joseph's available time
        joseph_meeting_end_time = joseph_end_time
        joseph_meeting_start_time = joseph_meeting_end_time - timedelta(minutes=min_meeting_time_joseph)
        
    # Update the itinerary with the adjusted meeting time
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Joseph",
        "start_time": joseph_meeting_start_time.strftime('%H:%M'),
        "end_time": joseph_meeting_end_time.strftime('%H:%M')
    })
    current_time = joseph_meeting_end_time + timedelta(minutes=travel_distances["Presidio"]["Sunset District"])
else:
    # If Joseph is not available, skip meeting Joseph
    print("Skipping meeting with Joseph")

# Meet Thomas
travel_time = travel_distances["Sunset District"]["Financial District"]
current_time += timedelta(minutes=travel_time)
itinerary.append({
    "action": "meet",
    "location": "Financial District",
    "person": "Thomas",
    "start_time": current_time.strftime('%H:%M'),
    "end_time": (current_time + timedelta(minutes=min_meeting_time_thomas)).strftime('%H:%M')
})
current_time += timedelta(minutes=min_meeting_time_thomas)
travel_time = travel_distances["Financial District"]["Sunset District"]
current_time += timedelta(minutes=travel_time)

# Ensure end time is within constraints
if current_time > kevin_end_time:
    current_time = kevin_end_time

# Add final travel time to Sunset District
travel_time = travel_distances["Financial District"]["Sunset District"]
current_time += timedelta(minutes=travel_time)

# Output result as JSON
result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=4))