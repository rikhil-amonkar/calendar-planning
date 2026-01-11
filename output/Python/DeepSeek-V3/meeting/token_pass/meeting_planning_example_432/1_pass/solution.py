import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MMAM' or 'H:MMPM' to minutes since midnight."""
    try:
        # Handle formats like '9:00AM' or '5:30PM'
        if 'AM' in t:
            hour_min = t.replace('AM', '').strip()
            hour, minute = map(int, hour_min.split(':'))
            if hour == 12:
                hour = 0
        elif 'PM' in t:
            hour_min = t.replace('PM', '').strip()
            hour, minute = map(int, hour_min.split(':'))
            if hour != 12:
                hour += 12
        else:
            hour, minute = map(int, t.split(':'))
        return hour * 60 + minute
    except Exception as e:
        raise ValueError(f"Invalid time format: {t}")

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' format."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times matrix (minutes)
    travel = {
        "Golden Gate Park": {
            "Fisherman's Wharf": 24,
            "Bayview": 23,
            "Mission District": 17,
            "Embarcadero": 25,
            "Financial District": 26
        },
        "Fisherman's Wharf": {
            "Golden Gate Park": 25,
            "Bayview": 26,
            "Mission District": 22,
            "Embarcadero": 8,
            "Financial District": 11
        },
        "Bayview": {
            "Golden Gate Park": 22,
            "Fisherman's Wharf": 25,
            "Mission District": 13,
            "Embarcadero": 19,
            "Financial District": 19
        },
        "Mission District": {
            "Golden Gate Park": 17,
            "Fisherman's Wharf": 22,
            "Bayview": 15,
            "Embarcadero": 19,
            "Financial District": 17
        },
        "Embarcadero": {
            "Golden Gate Park": 25,
            "Fisherman's Wharf": 6,
            "Bayview": 21,
            "Mission District": 20,
            "Financial District": 5
        },
        "Financial District": {
            "Golden Gate Park": 23,
            "Fisherman's Wharf": 10,
            "Bayview": 19,
            "Mission District": 17,
            "Embarcadero": 4
        }
    }

    # Friends data: name, location, window_start, window_end, min_duration (minutes)
    friends = [
        ("Joseph", "Fisherman's Wharf", "8:00AM", "5:30PM", 90),
        ("Jeffrey", "Bayview", "5:30PM", "9:30PM", 60),
        ("Kevin", "Mission District", "11:15AM", "3:15PM", 30),
        ("David", "Embarcadero", "8:15AM", "9:00AM", 30),
        ("Barbara", "Financial District", "10:30AM", "4:30PM", 15)
    ]

    # Convert times to minutes
    friends_min = []
    for name, loc, start, end, dur in friends:
        friends_min.append((name, loc, time_to_minutes(start), time_to_minutes(end), dur))

    # Start at Golden Gate Park at 9:00 AM
    start_time = time_to_minutes("9:00AM")
    start_loc = "Golden Gate Park"

    # David is impossible (window ends 9:00, we arrive earliest 9:25)
    # So only consider Joseph, Jeffrey, Kevin, Barbara
    possible_friends = [f for f in friends_min if f[0] != "David"]
    # We'll try permutations of these 4
    best_schedule = None
    best_count = 0

    for perm in itertools.permutations(possible_friends):
        current_time = start_time
        current_loc = start_loc
        schedule = []
        feasible = True

        for name, loc, win_start, win_end, min_dur in perm:
            # Travel to friend's location
            travel_time = travel[current_loc][loc]
            arrival = current_time + travel_time
            # Start meeting at max(arrival, win_start)
            meet_start = max(arrival, win_start)
            # Check if possible
            if meet_start + min_dur > win_end:
                feasible = False
                break
            meet_end = meet_start + min_dur
            schedule.append((name, loc, meet_start, meet_end))
            current_time = meet_end
            current_loc = loc

        if feasible and len(schedule) > best_count:
            best_count = len(schedule)
            best_schedule = schedule
        # Since we want max friends, stop if we found a schedule with all 4
        if best_count == 4:
            break

    # If no permutation works for all 4, try with 3, etc.
    # But let's first see if all 4 works.
    if best_schedule is None:
        # Fallback: try subsets
        for r in range(4, 0, -1):
            for subset in itertools.combinations(possible_friends, r):
                for perm in itertools.permutations(subset):
                    current_time = start_time
                    current_loc = start_loc
                    schedule = []
                    feasible = True
                    for name, loc, win_start, win_end, min_dur in perm:
                        travel_time = travel[current_loc][loc]
                        arrival = current_time + travel_time
                        meet_start = max(arrival, win_start)
                        if meet_start + min_dur > win_end:
                            feasible = False
                            break
                        meet_end = meet_start + min_dur
                        schedule.append((name, loc, meet_start, meet_end))
                        current_time = meet_end
                        current_loc = loc
                    if feasible:
                        best_schedule = schedule
                        best_count = r
                        break
                if best_schedule:
                    break
            if best_schedule:
                break

    # Convert best_schedule to output format
    itinerary = []
    for name, loc, meet_start, meet_end in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()