import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times between locations (in minutes)
    travel_times = {
        "Nob Hill": {"North Beach": 8, "Fisherman's Wharf": 11, "Bayview": 19},
        "North Beach": {"Nob Hill": 7, "Fisherman's Wharf": 5, "Bayview": 22},
        "Fisherman's Wharf": {"Nob Hill": 11, "North Beach": 6, "Bayview": 26},
        "Bayview": {"Nob Hill": 20, "North Beach": 21, "Fisherman's Wharf": 25}
    }
    
    # Meeting constraints and availability (times in minutes from midnight)
    # Format: time_str -> minutes. For example, 9:00 is 9*60 = 540.
    def time_to_minutes(time_str):
        parts = time_str.split(":")
        return int(parts[0]) * 60 + int(parts[1])
    
    # Starting at Nob Hill at 9:00
    start_location = "Nob Hill"
    start_time = time_to_minutes("9:00")
    
    # Friend constraints:
    constraints = {
        "Helen": {
            "location": "North Beach",
            "avail_start": time_to_minutes("7:00"),
            "avail_end": time_to_minutes("16:45"),
            "min_duration": 120
        },
        "Kimberly": {
            "location": "Fisherman's Wharf",
            "avail_start": time_to_minutes("16:30"),
            "avail_end": time_to_minutes("21:00"),
            "min_duration": 45
        },
        "Patricia": {
            "location": "Bayview",
            "avail_start": time_to_minutes("18:00"),
            "avail_end": time_to_minutes("21:15"),
            "min_duration": 120
        }
    }
    
    itinerary = []
    
    # 1. Schedule meeting with Helen at North Beach
    # Travel: Nob Hill -> North Beach
    travel_to_helen = travel_times[start_location]["North Beach"]
    arrival_time_helen = start_time + travel_to_helen
    # Meeting start is when you arrive, but must be within Helen's available window.
    meeting_start_helen = max(arrival_time_helen, constraints["Helen"]["avail_start"])
    meeting_end_helen = meeting_start_helen + constraints["Helen"]["min_duration"]
    # Ensure meeting does not exceed Helen's available end time (not enforced further here)
    
    itinerary.append({
        "action": "meet",
        "location": constraints["Helen"]["location"],
        "person": "Helen",
        "start_time": minutes_to_time_str(meeting_start_helen),
        "end_time": minutes_to_time_str(meeting_end_helen)
    })
    
    # 2. Schedule meeting with Kimberly at Fisherman's Wharf
    # Travel from Helen's location (North Beach) -> Fisherman's Wharf
    travel_to_kimberly = travel_times["North Beach"]["Fisherman's Wharf"]
    departure_after_helen = meeting_end_helen  # leave immediately after meeting
    arrival_time_kimberly = departure_after_helen + travel_to_kimberly
    # Kimberly is available from 16:30, so wait if necessary.
    meeting_start_kimberly = max(arrival_time_kimberly, constraints["Kimberly"]["avail_start"])
    meeting_end_kimberly = meeting_start_kimberly + constraints["Kimberly"]["min_duration"]
    
    itinerary.append({
        "action": "meet",
        "location": constraints["Kimberly"]["location"],
        "person": "Kimberly",
        "start_time": minutes_to_time_str(meeting_start_kimberly),
        "end_time": minutes_to_time_str(meeting_end_kimberly)
    })
    
    # 3. Schedule meeting with Patricia at Bayview
    # Travel from Kimberly's location (Fisherman's Wharf) -> Bayview
    travel_to_patricia = travel_times["Fisherman's Wharf"]["Bayview"]
    departure_after_kimberly = meeting_end_kimberly
    arrival_time_patricia = departure_after_kimberly + travel_to_patricia
    # Patricia is available starting at 18:00, so meeting starts when available.
    meeting_start_patricia = max(arrival_time_patricia, constraints["Patricia"]["avail_start"])
    meeting_end_patricia = meeting_start_patricia + constraints["Patricia"]["min_duration"]
    
    itinerary.append({
        "action": "meet",
        "location": constraints["Patricia"]["location"],
        "person": "Patricia",
        "start_time": minutes_to_time_str(meeting_start_patricia),
        "end_time": minutes_to_time_str(meeting_end_patricia)
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()