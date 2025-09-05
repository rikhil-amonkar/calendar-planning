import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def compute_schedule():
    # Travel times in minutes between locations (non-symmetric)
    travel_times = {
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Bayview"): 26,
        ("Richmond District", "Union Square"): 21,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Chinatown"): 16,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Union Square"): 16,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Union Square"): 7,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Union Square"): 9,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Marina District"): 25,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Union Square"): 17,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Bayview"): 15
    }
    
    # Meeting constraints. Times are in minutes since midnight.
    meetings = [
        {
            "person": "Kimberly",
            "location": "Marina District",
            "available_start": 13 * 60 + 15,  # 13:15 => 795
            "available_end": 16 * 60 + 45,    # 16:45 => 1005
            "duration": 15
        },
        {
            "person": "Robert",
            "location": "Chinatown",
            "available_start": 12 * 60 + 15,  # 12:15 => 735
            "available_end": 20 * 60 + 15,    # 20:15 => 1215
            "duration": 15
        },
        {
            "person": "Rebecca",
            "location": "Financial District",
            "available_start": 13 * 60 + 15,  # 13:15 => 795
            "available_end": 16 * 60 + 45,    # 16:45 => 1005
            "duration": 75
        },
        {
            "person": "Margaret",
            "location": "Bayview",
            "available_start": 9 * 60 + 30,   # 9:30 => 570
            "available_end": 13 * 60 + 30,    # 13:30 => 810
            "duration": 30
        },
        {
            "person": "Kenneth",
            "location": "Union Square",
            "available_start": 19 * 60 + 30,  # 19:30 => 1170
            "available_end": 21 * 60 + 15,    # 21:15 => 1275
            "duration": 75
        }
    ]
    
    # We start at Richmond District at 9:00AM (9*60 = 540 minutes)
    start_time = 9 * 60
    
    best_itinerary = None
    best_meetings_count = 0
    best_finish_time = float('inf')

    # Check all orders (permutations) of meetings
    for order in itertools.permutations(meetings):
        current_time = start_time
        current_location = "Richmond District"
        itinerary_current = []
        feasible = True
        for meet in order:
            key = (current_location, meet["location"])
            if key not in travel_times:
                feasible = False
                break
            travel = travel_times[key]
            arrival = current_time + travel
            # Wait if arrived before the meeting's available start time
            meeting_start = max(arrival, meet["available_start"])
            meeting_end = meeting_start + meet["duration"]
            if meeting_end > meet["available_end"]:
                feasible = False
                break
            itinerary_current.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            })
            current_time = meeting_end
            current_location = meet["location"]
        if feasible:
            meetings_count = len(itinerary_current)
            # Primary goal: maximize number of meetings; secondary: finish as early as possible
            if meetings_count > best_meetings_count or (meetings_count == best_meetings_count and current_time < best_finish_time):
                best_meetings_count = meetings_count
                best_finish_time = current_time
                best_itinerary = itinerary_current

    result = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    compute_schedule()