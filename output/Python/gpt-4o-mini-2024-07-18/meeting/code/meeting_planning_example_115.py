import json
from datetime import datetime, timedelta

# Constants for travel time between districts in minutes
TRAVEL_TIMES = {
    ('Richmond', 'Pacific Heights'): 10,
    ('Richmond', 'Marina'): 9,
    ('Pacific Heights', 'Richmond'): 12,
    ('Pacific Heights', 'Marina'): 6,
    ('Marina', 'Richmond'): 11,
    ('Marina', 'Pacific Heights'): 7,
}

# Meeting constraints
arrival_time = datetime.strptime("09:00", "%H:%M")
jessica_start = datetime.strptime("15:30", "%H:%M")
jessica_end = datetime.strptime("16:45", "%H:%M")
carol_start = datetime.strptime("11:30", "%H:%M")
carol_end = datetime.strptime("15:00", "%H:%M")
meet_jessica_duration = timedelta(minutes=45)
meet_carol_duration = timedelta(minutes=60)

# Function to compute the itinerary
def compute_itinerary():
    itinerary = []
    current_time = arrival_time

    # Schedule meeting with Carol at Marina
    travel_to_marina = TRAVEL_TIMES[('Richmond', 'Marina')]
    arrive_at_marina = current_time + timedelta(minutes=travel_to_marina)

    if arrive_at_marina < carol_start:
        # Wait until Carol is available
        current_time = carol_start

    # Schedule meeting with Carol from current_time
    meet_carol_start = current_time
    meet_carol_end = meet_carol_start + meet_carol_duration

    if meet_carol_end > carol_end:
        # Adjust if meeting with Carol extends beyond her availability
        meet_carol_end = carol_end

    itinerary.append({
        "action": "meet",
        "location": "Marina",
        "person": "Carol",
        "start_time": meet_carol_start.strftime("%H:%M"),
        "end_time": meet_carol_end.strftime("%H:%M"),
    })

    # Update current time after meeting with Carol
    current_time = meet_carol_end

    # Travel to Pacific Heights to meet Jessica
    travel_to_pacific_heights = TRAVEL_TIMES[('Marina', 'Pacific Heights')]
    arrive_at_pacific_heights = current_time + timedelta(minutes=travel_to_pacific_heights)

    if arrive_at_pacific_heights < jessica_start:
        # Wait until Jessica is available
        current_time = jessica_start
    else:
        current_time = arrive_at_pacific_heights

    # Schedule meeting with Jessica
    meet_jessica_start = current_time
    meet_jessica_end = meet_jessica_start + meet_jessica_duration

    if meet_jessica_end > jessica_end:
        # Adjust if meeting with Jessica extends beyond her availability
        meet_jessica_end = jessica_end

    itinerary.append({
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Jessica",
        "start_time": meet_jessica_start.strftime("%H:%M"),
        "end_time": meet_jessica_end.strftime("%H:%M"),
    })

    return {"itinerary": itinerary}

# Get the optimal meeting schedule
optimal_schedule = compute_itinerary()

# Output the result as a JSON-formatted dictionary
print(json.dumps(optimal_schedule, indent=2))