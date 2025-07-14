# Define the friends' availability and travel times
friends_availability = {
    "Daniel": {"location": "Nob Hill", "start": 8*60 + 15, "end": 11*60, "duration": 15},
    "Kevin": {"location": "Chinatown", "start": 12*60, "end": 19*60, "duration": 30},
    "Timothy": {"location": "Pacific Heights", "start": 12*60, "end": 18*60, "duration": 90},
    "Steven": {"location": "Marina District", "start": 16*60 + 30, "end": 20*60 + 45, "duration": 90},
    "Ashley": {"location": "Golden Gate Park", "start": 20*60 + 45, "end": 21*60 + 45, "duration": 60},
    "Elizabeth": {"location": "Presidio", "start": 21*60 + 15, "end": 22*60 + 15, "duration": 45},
}

travel_times = {
    ("Mission District", "Nob Hill"): 12,
    ("Nob Hill", "Chinatown"): 6,
    ("Chinatown", "Pacific Heights"): 11,
    ("Pacific Heights", "Marina District"): 7,
    ("Marina District", "Golden Gate Park"): 18,
    ("Golden Gate Park", "Presidio"): 12,
}

# Define the schedule
schedule = [
    ("Daniel", 9*60 + 12, 9*60 + 12 + 15),  # 9:12 AM - 9:27 AM
    ("Kevin", 12*60, 12*60 + 30),           # 12:00 PM - 12:30 PM
    ("Timothy", 12*60 + 30, 12*60 + 30 + 90), # 12:30 PM - 2:00 PM
    ("Steven", 16*60 + 30, 16*60 + 30 + 90), # 4:30 PM - 6:00 PM
    ("Ashley", 20*60, 20*60 + 60),             # 6:00 PM - 7:00 PM
    ("Elizabeth", 21*60, 21*60 + 45)          # 7:00 PM - 7:45 PM
]

# Print the schedule
print("SOLUTION:")
for friend, arrival, departure in schedule:
    print(f"{friend}: {arrival // 60}:{arrival % 60:02} - {departure // 60}:{departure % 60:02}")