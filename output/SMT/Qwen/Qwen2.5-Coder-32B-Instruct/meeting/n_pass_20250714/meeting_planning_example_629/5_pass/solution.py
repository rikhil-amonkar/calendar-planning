# Define the manual schedule
schedule = {
    "Russian Hill": {"arrival": 9*60, "meeting": 0},
    "Chinatown": {"arrival": 9*60 + 9, "meeting": 9*60 + 15, "duration": 90},
    "Pacific Heights": {"arrival": 9*60 + 15 + 90 + 10, "meeting": 14*60 + 15, "duration": 15},
    "Golden Gate Park": {"arrival": 14*60 + 15 + 15 + 15, "meeting": 15*60 + 45, "duration": 135},
    "Presidio": {"arrival": 15*60 + 45 + 135 + 12, "meeting": 18*60 + 12, "duration": 90},
    "Bayview": {"arrival": 18*60 + 12 + 90 + 31, "meeting": 19*60 + 13, "duration": 30},
    "Richmond District": {"arrival": 19*60 + 13 + 30 + 25, "meeting": 20*60 + 8, "duration": 60}
}

# Calculate the total time spent meeting friends
total_meetings = sum([info["duration"] for info in schedule.values() if "duration" in info])

# Print the schedule and total meetings
print("SOLUTION:")
for loc, info in schedule.items():
    if "meeting" in info:
        print(f"{loc}: Arrive at {info['arrival'] // 60}:{info['arrival'] % 60:02d}, Meet from {info['meeting'] // 60}:{info['meeting'] % 60:02d} for {info['duration']} minutes")
    else:
        print(f"{loc}: Arrive at {info['arrival'] // 60}:{info['arrival'] % 60:02d}")
print(f"Total meetings: {total_meetings} minutes")