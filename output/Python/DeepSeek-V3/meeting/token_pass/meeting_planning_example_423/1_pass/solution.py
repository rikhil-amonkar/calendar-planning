import itertools
import json

def time_to_min(t):
    """Convert 'H:MM' string to minutes from midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    """Convert minutes from midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times matrix (in minutes)
locations = ["Presidio", "Richmond District", "North Beach", "Financial District", "Golden Gate Park", "Union Square"]
travel = {
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Union Square"): 22,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Union Square"): 21,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Union Square"): 7,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Union Square"): 9,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "North Beach"): 24,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Union Square"): 22,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
}

# Friend data: name, location, window start, window end, min duration (minutes)
friends = [
    ("Jason", "Richmond District", time_to_min("13:00"), time_to_min("20:45"), 90),
    ("Melissa", "North Beach", time_to_min("18:45"), time_to_min("20:15"), 45),
    ("Brian", "Financial District", time_to_min("9:45"), time_to_min("21:45"), 15),
    ("Elizabeth", "Golden Gate Park", time_to_min("8:45"), time_to_min("21:30"), 105),
    ("Laura", "Union Square", time_to_min("14:15"), time_to_min("19:30"), 75),
]

# Start at Presidio at 9:00 AM = 540 min from midnight
start_time = time_to_min("9:00")
current_loc = "Presidio"
current_time = start_time

# Try to meet all 5
best_schedule = None
best_count = 0

# All permutations of 5 friends
for perm in itertools.permutations(range(5)):
    schedule = []
    loc = current_loc
    time = current_time
    possible = True
    for idx in perm:
        name, place, win_start, win_end, dur = friends[idx]
        # Travel time
        travel_time = travel.get((loc, place))
        if travel_time is None:
            # If same location (shouldn't happen here)
            travel_time = 0
        time += travel_time
        # Arrival at place
        if time > win_end - dur:
            possible = False
            break
        start_meeting = max(time, win_start)
        end_meeting = start_meeting + dur
        if end_meeting > win_end:
            possible = False
            break
        schedule.append((name, place, start_meeting, end_meeting))
        time = end_meeting
        loc = place
    if possible:
        if len(schedule) == 5:
            best_schedule = schedule
            break
        elif len(schedule) > best_count:
            best_count = len(schedule)
            best_schedule = schedule

# If best_schedule is None, try subsets (but code above already does by permutation breaking early)
# Let's ensure we have a valid schedule
if best_schedule is None:
    # Fallback: meet as many as possible by brute force over subsets
    for size in range(5, 0, -1):
        for subset in itertools.combinations(range(5), size):
            for perm in itertools.permutations(subset):
                schedule = []
                loc = current_loc
                time = current_time
                possible = True
                for idx in perm:
                    name, place, win_start, win_end, dur = friends[idx]
                    travel_time = travel.get((loc, place), 0)
                    time += travel_time
                    if time > win_end - dur:
                        possible = False
                        break
                    start_meeting = max(time, win_start)
                    end_meeting = start_meeting + dur
                    if end_meeting > win_end:
                        possible = False
                        break
                    schedule.append((name, place, start_meeting, end_meeting))
                    time = end_meeting
                    loc = place
                if possible:
                    best_schedule = schedule
                    break
            if best_schedule:
                break
        if best_schedule:
            break

# Format output
itinerary = []
for name, place, start_m, end_m in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": place,
        "person": name,
        "start_time": min_to_time(start_m),
        "end_time": min_to_time(end_m)
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))