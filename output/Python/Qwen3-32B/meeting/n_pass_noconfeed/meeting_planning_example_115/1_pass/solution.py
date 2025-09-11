import json

def time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Marina District'): 6,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Pacific Heights'): 7,
}

current_location = 'Richmond District'
current_time = 9 * 60  # 540 minutes (9:00 AM)
itinerary = []

# First, go to Marina District to meet Carol
travel_time = travel_times[(current_location, 'Marina District')]
current_time += travel_time
current_location = 'Marina District'

# Now, schedule meeting with Carol
carol_start_available = 11 * 60 + 30  # 690 mins (11:30 AM)
carol_end_available = 15 * 60  # 3:00 PM → 900 mins
carol_min_duration = 60  # minutes

carol_start = max(current_time, carol_start_available)

# Check if there is enough time to have the meeting before her end time
if carol_start + carol_min_duration <= carol_end_available:
    carol_end = carol_start + carol_min_duration
    itinerary.append({
        "action": "meet",
        "location": "Marina District",
        "person": "Carol",
        "start_time": time_str(carol_start),
        "end_time": time_str(carol_end)
    })
    current_time = carol_end
    current_location = 'Marina District'

# Now, travel to Pacific Heights for Jessica
if itinerary:  # Only if met Carol
    travel_time = travel_times[(current_location, 'Pacific Heights')]
    current_time += travel_time
    current_location = 'Pacific Heights'

    # Now, schedule meeting with Jessica
    jessica_start_available = 15 * 60 + 30  # 3:30 PM → 930 mins
    jessica_end_available = 16 * 60 + 45  # 4:45 PM → 1005 mins
    jessica_min_duration = 45

    jessica_start = max(current_time, jessica_start_available)
    jessica_end = jessica_start + jessica_min_duration

    if jessica_end <= jessica_end_available:
        itinerary.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Jessica",
            "start_time": time_str(jessica_start),
            "end_time": time_str(jessica_end)
        })

# Output JSON
print(json.dumps({"itinerary": itinerary}, indent=2))