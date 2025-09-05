import json
import itertools

# Define travel times (all times in minutes)
travel_times = {
    "Financial District": {"Fisherman's Wharf": 10, "Pacific Heights": 13, "Mission District": 17},
    "Fisherman's Wharf": {"Financial District": 11, "Pacific Heights": 12, "Mission District": 22},
    "Pacific Heights": {"Financial District": 13, "Fisherman's Wharf": 13, "Mission District": 15},
    "Mission District": {"Financial District": 17, "Fisherman's Wharf": 22, "Pacific Heights": 16}
}

# Participant meeting constraints: times in minutes from midnight.
# 9:00 is 540, 10:45 is 645, 12:15 is 735, 15:30 is 930, 7:45PM is 19*60+45 = 1185.
participants = {
    "Timothy": {
        "location": "Pacific Heights",
        "available_start": 540,   # 9:00
        "available_end": 930,     # 15:30
        "min_duration": 75
    },
    "David": {
        "location": "Fisherman's Wharf",
        "available_start": 645,   # 10:45
        "available_end": 930,     # 15:30
        "min_duration": 15
    },
    "Robert": {
        "location": "Mission District",
        "available_start": 735,   # 12:15
        "available_end": 1185,    # 19:45
        "min_duration": 90
    }
}

# Starting point at Financial District at 9:00 (540 minutes)
start_location = "Financial District"
start_time = 540

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def simulate_schedule(order):
    """
    Given an order (list of person names), simulate the meeting schedule.
    Returns (itinerary, finishing_time) if valid, otherwise None.
    """
    current_time = start_time
    current_location = start_location
    itinerary = []
    
    for person in order:
        info = participants[person]
        destination = info["location"]
        # Get travel time from current location to destination
        travel_time = travel_times[current_location][destination]
        arrival_time = current_time + travel_time
        # Can only start meeting when friend is available
        meeting_start = max(arrival_time, info["available_start"])
        meeting_end = meeting_start + info["min_duration"]
        # Check if meeting can finish before the friend leaves
        if meeting_end > info["available_end"]:
            return None
        # Append the meeting event
        event = {
            "action": "meet",
            "location": destination,
            "person": person,
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        }
        itinerary.append(event)
        # Update current time and location for next meeting
        current_time = meeting_end
        current_location = destination

    return itinerary, current_time

def find_best_schedule():
    person_names = list(participants.keys())
    best_itinerary = None
    best_finish_time = None
    best_meet_count = 0

    # Try all permutations of meeting order
    for order in itertools.permutations(person_names):
        result = simulate_schedule(order)
        if result is None:
            continue  # this order is not feasible
        itinerary, finish_time = result
        meet_count = len(itinerary)
        # We want to maximize number of meetings; if equal, choose the earliest finish time.
        if meet_count > best_meet_count or (meet_count == best_meet_count and (best_finish_time is None or finish_time < best_finish_time)):
            best_meet_count = meet_count
            best_finish_time = finish_time
            best_itinerary = itinerary
    return best_itinerary

def main():
    itinerary = find_best_schedule()
    if itinerary is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()