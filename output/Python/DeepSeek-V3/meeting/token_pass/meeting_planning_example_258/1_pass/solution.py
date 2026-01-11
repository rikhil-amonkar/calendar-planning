import json
import itertools

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Travel times in minutes between locations
    travel = {
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18,
    }

    # Friend data: name, location, start, end, min_duration
    friends = [
        ("Betty", "Presidio", "10:15", "21:30", 45),
        ("David", "Richmond District", "13:00", "20:15", 90),
        ("Barbara", "Fisherman's Wharf", "9:15", "20:15", 120),
    ]

    # Convert times to minutes
    friends_min = []
    for name, loc, start, end, dur in friends:
        friends_min.append((name, loc, time_to_minutes(start), time_to_minutes(end), dur))

    start_loc = "Embarcadero"
    start_time = time_to_minutes("9:00")

    best_itinerary = []
    max_met = 0

    # Try meeting all 3 first
    for perm in itertools.permutations(range(3)):
        current_loc = start_loc
        current_time = start_time
        itinerary = []
        possible = True
        for idx in perm:
            name, loc, f_start, f_end, dur = friends_min[idx]
            # Travel to friend's location
            travel_time = travel[(current_loc, loc)]
            arrive = current_time + travel_time
            # Wait if early
            start_meeting = max(arrive, f_start)
            # Check if enough time before friend leaves
            if start_meeting + dur > f_end:
                possible = False
                break
            end_meeting = start_meeting + dur
            itinerary.append((name, loc, start_meeting, end_meeting))
            current_loc = loc
            current_time = end_meeting
        if possible:
            if len(itinerary) > max_met:
                max_met = len(itinerary)
                best_itinerary = itinerary
            # If we met all 3, we can stop searching permutations
            if len(itinerary) == 3:
                break

    # If all 3 not possible, try subsets of size 2
    if max_met < 3:
        best_itinerary = []
        max_met = 0
        for perm in itertools.permutations(range(3), 2):
            current_loc = start_loc
            current_time = start_time
            itinerary = []
            possible = True
            for idx in perm:
                name, loc, f_start, f_end, dur = friends_min[idx]
                travel_time = travel[(current_loc, loc)]
                arrive = current_time + travel_time
                start_meeting = max(arrive, f_start)
                if start_meeting + dur > f_end:
                    possible = False
                    break
                end_meeting = start_meeting + dur
                itinerary.append((name, loc, start_meeting, end_meeting))
                current_loc = loc
                current_time = end_meeting
            if possible and len(itinerary) > max_met:
                max_met = len(itinerary)
                best_itinerary = itinerary

    # Format output
    result = {"itinerary": []}
    for name, loc, start_m, end_m in best_itinerary:
        result["itinerary"].append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time(start_m),
            "end_time": minutes_to_time(end_m)
        })

    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()