import json
from datetime import datetime, timedelta

# Constants
CASTRO_START_TIME = 9 * 60  # 9:00 AM in minutes
MIN_MEETING_DURATION = 90  # 90 minutes

# Locations and their indices
locations = ["The Castro", "Bayview", "Pacific Heights", "Alamo Square", "Fisherman's Wharf", "Golden Gate Park"]
location_indices = {loc: i for i, loc in enumerate(locations)}

# Travel times matrix (in minutes)
travel_times = [
    [0, 19, 16, 8, 24, 11],  # The Castro
    [20, 0, 23, 16, 25, 22],  # Bayview
    [16, 22, 0, 10, 13, 15],  # Pacific Heights
    [8, 16, 10, 0, 19, 9],    # Alamo Square
    [26, 26, 12, 20, 0, 25],  # Fisherman's Wharf
    [13, 23, 16, 10, 24, 0]   # Golden Gate Park
]

# Friends' availability (start and end times in minutes since midnight)
availability = {
    "Rebecca": (9 * 60, 12 * 60 + 45),  # 9:00 AM to 12:45 PM
    "Amanda": (18 * 60 + 30, 21 * 60 + 45),  # 6:30 PM to 9:45 PM
    "James": (9 * 60 + 45, 21 * 60 + 15),  # 9:45 AM to 9:15 PM
    "Sarah": (8 * 60, 21 * 60 + 30),  # 8:00 AM to 9:30 PM
    "Melissa": (9 * 60, 18 * 60 + 45)  # 9:00 AM to 6:45 PM
}

def time_to_minutes(time_str):
    """Converts time in 'H:MM' format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight to 'H:MM' format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes}"

def get_feasible_meeting_times(availability):
    """Generates feasible meeting times for each friend."""
    feasible_times = {}
    for name, (start, end) in availability.items():
        feasible_times[name] = []
        current_start = max(start, CASTRO_START_TIME)
        while current_start + MIN_MEETING_DURATION <= end:
            feasible_times[name].append((current_start, current_start + MIN_MEETING_DURATION))
            current_start += 1
    return feasible_times

def find_optimal_schedule(feasible_times):
    """Finds the optimal schedule based on the feasible meeting times."""
    def dfs(current_location, current_time, visited, itinerary):
        if len(visited) == len(feasible_times):
            return itinerary
        
        best_itinerary = None
        for name, times in feasible_times.items():
            if name in visited:
                continue
            for start, end in times:
                travel_time = travel_times[location_indices[current_location]][location_indices[locations[0]]]
                if current_time + travel_time + MIN_MEETING_DURATION <= start:
                    new_itinerary = dfs(locations[0], end, visited | {name}, itinerary + [{
                        "action": "meet",
                        "location": locations[0],
                        "person": name,
                        "start_time": minutes_to_time(start),
                        "end_time": minutes_to_time(end)
                    }])
                    if best_itinerary is None or len(new_itinerary) > len(best_itinerary):
                        best_itinerary = new_itinerary
        return best_itinerary
    
    feasible_times = get_feasible_meeting_times(availability)
    return dfs("The Castro", CASTRO_START_TIME, set(), [])

def main():
    feasible_times = get_feasible_meeting_times(availability)
    optimal_schedule = find_optimal_schedule(feasible_times)
    print(json.dumps({"itinerary": optimal_schedule}, indent=2))

if __name__ == "__main__":
    main()