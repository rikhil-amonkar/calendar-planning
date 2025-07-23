import itertools
import json

def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1]) if len(parts) > 1 else 0
        return hours * 60 + minutes

    # Convert minutes back to time string (H:MM format)
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Travel times dictionary
    travel_times = {
        "Nob Hill": {
            "Richmond District": 14,
            "Financial District": 9,
            "North Beach": 8,
            "The Castro": 17,
            "Golden Gate Park": 17
        },
        "Richmond District": {
            "Nob Hill": 17,
            "Financial District": 22,
            "North Beach": 17,
            "The Castro": 16,
            "Golden Gate Park": 9
        },
        "Financial District": {
            "Nob Hill": 8,
            "Richmond District": 21,
            "North Beach": 7,
            "The Castro": 23,
            "Golden Gate Park": 23
        },
        "North Beach": {
            "Nob Hill": 7,
            "Richmond District": 18,
            "Financial District": 8,
            "The Castro": 22,
            "Golden Gate Park": 22
        },
        "The Castro": {
            "Nob Hill": 16,
            "Richmond District": 16,
            "Financial District": 20,
            "North Beach": 20,
            "Golden Gate Park": 11
        },
        "Golden Gate Park": {
            "Nob Hill": 20,
            "Richmond District": 7,
            "Financial District": 26,
            "North Beach": 24,
            "The Castro": 13
        }
    }

    # Meeting constraints
    meetings = [
        {"person": "Emily", "location": "Richmond District", "available_start": time_to_minutes("19:00"), "available_end": time_to_minutes("21:00"), "min_duration": 15},
        {"person": "Margaret", "location": "Financial District", "available_start": time_to_minutes("16:30"), "available_end": time_to_minutes("20:15"), "min_duration": 75},
        {"person": "Ronald", "location": "North Beach", "available_start": time_to_minutes("18:30"), "available_end": time_to_minutes("19:30"), "min_duration": 45},
        {"person": "Deborah", "location": "The Castro", "available_start": time_to_minutes("13:45"), "available_end": time_to_minutes("21:15"), "min_duration": 90},
        {"person": "Jeffrey", "location": "Golden Gate Park", "available_start": time_to_minutes("11:15"), "available_end": time_to_minutes("14:30"), "min_duration": 120}
    ]

    # Initial state
    start_location = "Nob Hill"
    start_time = time_to_minutes("9:00")

    best_count = 0
    best_schedule = None

    # Try all permutations of meetings
    for perm in itertools.permutations(meetings):
        current_loc = start_location
        current_time = start_time
        scheduled = []
        
        for meet in perm:
            # Get travel time to meeting location
            travel_time = travel_times[current_loc][meet["location"]]
            arrival_time = current_time + travel_time
            # Calculate meeting start and end times
            meet_start = max(arrival_time, meet["available_start"])
            meet_end = meet_start + meet["min_duration"]
            
            # Check if meeting fits in availability window
            if meet_end <= meet["available_end"]:
                scheduled.append({
                    "person": meet["person"],
                    "location": meet["location"],
                    "start": meet_start,
                    "end": meet_end
                })
                current_time = meet_end
                current_loc = meet["location"]
        
        # Update best schedule if this permutation schedules more meetings
        if len(scheduled) > best_count:
            best_count = len(scheduled)
            best_schedule = scheduled

    # Convert best schedule to output format
    itinerary = []
    for meet in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": minutes_to_time(meet["start"]),
            "end_time": minutes_to_time(meet["end"])
        })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()