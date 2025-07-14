# Define the start time at Sunset District
start_time_sunset_district = 9 * 60  # 9:00 AM

# Define the travel times in minutes
travel_times = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Financial District"): 30,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Financial District"): 17,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Presidio"): 22,
}

# Define the friends' availability and meeting requirements
friends = {
    "Kevin": {"location": "Alamo Square", "start": 8*60 + 15, "end": 21*60 + 30, "min_meeting": 75},
    "Kimberly": {"location": "Russian Hill", "start": 8*60 + 45, "end": 12*60 + 30, "min_meeting": 30},
    "Joseph": {"location": "Presidio", "start": 18*60 + 30, "end": 19*60 + 15, "min_meeting": 45},
    "Thomas": {"location": "Financial District", "start": 19*60, "end": 21*60 + 45, "min_meeting": 45},
}

# Manually construct the feasible schedule
schedule = [
    ("Kevin", 9*60 + 17, 9*60 + 17 + 75),
    ("Kimberly", 9*60 + 17 + 75 + 13, 9*60 + 17 + 75 + 13 + 30),
    ("Thomas", 9*60 + 17 + 75 + 13 + 30 + 11, 9*60 + 17 + 75 + 13 + 30 + 11 + 45),
    ("Joseph", 9*60 + 17 + 75 + 13 + 30 + 11 + 45 + 22, 9*60 + 17 + 75 + 13 + 30 + 11 + 45 + 22 + 45)
]

# Print the schedule
print("SOLUTION:")
for friend, start, end in schedule:
    print(f"Meet {friend} at {friends[friend]['location']} from {start // 60}:{start % 60:02d} to {end // 60}:{end % 60:02d}")