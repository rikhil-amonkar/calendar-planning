# SOLUTION:
import json
from dataclasses import dataclass
from typing import Dict, Tuple, List, Optional

def parse_time(s: str) -> int:
    h, m = s.strip().split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

@dataclass
class Friend:
    name: str
    location: str
    available_start: int
    available_end: int
    min_meet: int

@dataclass
class State:
    current_location: str
    current_time: int

def compute_best_meeting(state: State, friend: Friend, travel_times: Dict[Tuple[str, str], int]) -> Optional[Tuple[int, int]]:
    # Determine travel time from current location to friend's location
    travel_time = travel_times.get((state.current_location, friend.location), None)
    if travel_time is None:
        return None  # cannot travel
    
    # Earliest we can arrive at friend's location
    earliest_arrival = state.current_time + travel_time
    
    # Meeting window candidate start times must be:
    # - Not earlier than friend's available start
    # - Not earlier than earliest arrival at the meeting location
    start_lower_bound = max(friend.available_start, earliest_arrival)
    
    # The latest possible start time to still meet min_meet within availability
    latest_start = friend.available_end - friend.min_meet
    if start_lower_bound > latest_start:
        return None  # infeasible
    
    # Enumerate possible start times minute-by-minute, and always end at availability end to maximize duration
    # Objective: maximize meeting duration; tie-breaker: earliest start time
    best = None
    best_duration = -1
    for s in range(start_lower_bound, latest_start + 1):
        # Ensure we can depart in time to reach s
        if s - travel_time < state.current_time:
            continue
        e = friend.available_end
        duration = e - s
        if duration >= friend.min_meet and duration > best_duration:
            best_duration = duration
            best = (s, e)
    return best

def main():
    # Input variables
    arrival_location = "Golden Gate Park"
    arrival_time_str = "9:00"
    travel_times = {
        ("Golden Gate Park", "Chinatown"): 23,
        ("Chinatown", "Golden Gate Park"): 23
    }
    friend_data = {
        "name": "David",
        "location": "Chinatown",
        "available_start": "16:00",
        "available_end": "21:45",
        "min_meet": 105
    }
    
    # Convert inputs
    state = State(current_location=arrival_location, current_time=parse_time(arrival_time_str))
    friend = Friend(
        name=friend_data["name"],
        location=friend_data["location"],
        available_start=parse_time(friend_data["available_start"]),
        available_end=parse_time(friend_data["available_end"]),
        min_meet=friend_data["min_meet"]
    )
    
    # Compute optimal schedule (maximize number of friends met; with single friend, maximize duration)
    best_window = compute_best_meeting(state, friend, travel_times)
    
    itinerary: List[Dict] = []
    if best_window is not None:
        s, e = best_window
        itinerary.append({
            "action": "meet",
            "location": friend.location,
            "person": friend.name,
            "start_time": fmt_time(s),
            "end_time": fmt_time(e),
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()