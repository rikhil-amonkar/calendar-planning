# Define the manual schedule
manual_schedule = {
    "Deborah": 10*60,  # Arrive at Chinatown at 10:00 AM
    "George": 10*60 + 15,  # Arrive at The Castro at 10:15 AM
    "Steven": 11*60 + 15,  # Arrive at Golden Gate Park at 11:15 AM
    "Emily": 12*60 + 15,  # Arrive at Russian Hill at 12:15 PM
    "Mark": 14*60 + 45,  # Arrive at Presidio at 2:45 PM
    "Andrew": 20*60 + 15  # Arrive at Embarcadero at 8:15 PM
}

# Define the friends and their constraints
friends = {
    "Emily": {"location": "Russian Hill", "start": 12*60 + 15, "end": 2*60 + 15, "min_meeting_time": 105},
    "Mark": {"location": "Presidio", "start": 2*60 + 45, "end": 7*60 + 30, "min_meeting_time": 60},
    "Deborah": {"location": "Chinatown", "start": 7*60 + 30, "end": 3*60 + 30, "min_meeting_time": 45},
    "Margaret": {"location": "Sunset District", "start": 21*60 + 30, "end": 22*60 + 30, "min_meeting_time": 60},
    "George": {"location": "The Castro", "start": 7*60 + 30, "end": 2*60 + 15, "min_meeting_time": 60},
    "Andrew": {"location": "Embarcadero", "start": 20*60 + 15, "end": 22*60, "min_meeting_time": 75},
    "Steven": {"location": "Golden Gate Park", "start": 11*60 + 15, "end": 21*60 + 15, "min_meeting_time": 105},
}

# Verify the manual schedule
schedule = []
for friend, time in manual_schedule.items():
    loc = friends[friend]["location"]
    start = friends[friend]["start"]
    end = friends[friend]["end"]
    min_meeting_time = friends[friend]["min_meeting_time"]
    
    if time <= end - min_meeting_time and time + min_meeting_time <= end:
        schedule.append((loc, time))
    else:
        print(f"Constraint violation for {friend} at {loc}")

# Sort the schedule by arrival time
schedule.sort(key=lambda x: x[1])

# Print the final schedule
print("SOLUTION:")
for loc, time in schedule:
    print(f"{loc}: {time // 60}:{time % 60:02d}")
print("\nFriends met:")
for friend, time in manual_schedule.items():
    if friends[friend]["location"] in [loc for loc, _ in schedule]:
        print(friend)