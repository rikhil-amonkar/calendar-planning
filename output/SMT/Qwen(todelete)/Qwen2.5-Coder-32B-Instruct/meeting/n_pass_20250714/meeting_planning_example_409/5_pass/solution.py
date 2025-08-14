# Manually constructed schedule
schedule = {
    "Laura": {"start_time": 9.25, "end_time": 9.75, "location": "Nob Hill", "duration": 0.5},
    "Patricia": {"start_time": 17.5, "end_time": 18.25, "location": "Embarcadero", "duration": 0.75},
    "Thomas": {"start_time": 16.0, "end_time": 18.0, "location": "Bayview", "duration": 2},
    "Stephanie": {"start_time": 18.0, "end_time": 18.5, "location": "Golden Gate Park", "duration": 0.5},
    "Betty": {"start_time": 18.5, "end_time": 19.25, "location": "Marina District", "duration": 0.75}
}

print("SOLUTION:")
for friend, details in schedule.items():
    print(f"{friend}: Start at {details['start_time']}PM, End at {details['end_time']}PM, Location: {details['location']}, Duration: {details['duration']} hours")