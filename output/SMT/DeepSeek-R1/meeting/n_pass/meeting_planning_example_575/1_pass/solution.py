import itertools
import json

# Define travel times between locations (7x7 matrix: 0=Castro, 1=Presidio, 2=Sunset, 3=Haight-Ashbury, 4=Mission, 5=Golden Gate Park, 6=Russian Hill)
travel_matrix = [
    [0, 20, 17, 6, 7, 11, 18],   # From Castro
    [21, 0, 15, 15, 26, 12, 14],  # From Presidio
    [17, 16, 0, 15, 24, 11, 24],  # From Sunset
    [6, 15, 15, 0, 11, 7, 17],    # From Haight-Ashbury
    [7, 25, 24, 12, 0, 17, 15],   # From Mission
    [13, 11, 10, 7, 17, 0, 19],   # From Golden Gate Park
    [21, 14, 23, 17, 16, 21, 0]   # From Russian Hill
]

# Define friends: (name, location_index, available_start, available_end, min_duration)
friends = [
    ("Rebecca", 1, 1095, 1245, 60),    # Presidio: 18:15 to 20:45 (1095 to 1245 min)
    ("Linda", 2, 930, 1185, 30),       # Sunset: 15:30 to 19:45 (930 to 1185 min)
    ("Elizabeth", 3, 1035, 1170, 105), # Haight-Ashbury: 17:15 to 19:30 (1035 to 1170 min)
    ("William", 4, 795, 1170, 30),     # Mission: 13:15 to 19:30 (795 to 1170 min)
    ("Robert", 5, 855, 1290, 45),      # Golden Gate Park: 14:15 to 21:30 (855 to 1290 min)
    ("Mark", 6, 600, 1275, 75)         # Russian Hill: 10:00 to 21:15 (600 to 1275 min)
]

start_time_castro = 540  # 9:00 AM in minutes

# Try subsets from largest (size 6) to smallest (size 1)
n = len(friends)
found_schedule = None

for k in range(n, 0, -1):
    for subset_indices in itertools.combinations(range(n), k):
        for perm in itertools.permutations(subset_indices):
            current_time = start_time_castro
            prev_loc = 0  # Start at Castro (index 0)
            schedule = []  # List of meetings in order
            valid = True
            
            for idx in perm:
                friend = friends[idx]
                loc = friend[1]
                # Travel from previous location to current friend's location
                travel_time = travel_matrix[prev_loc][loc]
                current_time += travel_time
                # Arrival time at friend's location
                arrival = current_time
                # Start time is max of arrival and friend's available start time
                start_meeting = max(arrival, friend[2])
                end_meeting = start_meeting + friend[4]
                # Check if meeting can be completed within friend's window
                if end_meeting > friend[3]:
                    valid = False
                    break
                # Record meeting details
                schedule.append((friend[0], start_meeting, end_meeting))
                current_time = end_meeting
                prev_loc = loc  # Update previous location for next travel
            
            if valid:
                found_schedule = schedule
                break
        if found_schedule:
            break
    if found_schedule:
        break

# Format the result
itinerary = []
if found_schedule:
    for meeting in found_schedule:
        name, start_meeting, end_meeting = meeting
        start_hour = start_meeting // 60
        start_minute = start_meeting % 60
        end_hour = end_meeting // 60
        end_minute = end_meeting % 60
        start_str = f"{start_hour:02d}:{start_minute:02d}"
        end_str = f"{end_hour:02d}:{end_minute:02d}"
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": start_str,
            "end_time": end_str
        })

result = {"itinerary": itinerary}
print("SOLUTION:")
print(json.dumps(result, indent=2))