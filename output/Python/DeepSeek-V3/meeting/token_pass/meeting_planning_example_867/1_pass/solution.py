import itertools
import json

def time_to_minutes(t):
    """Convert 'H:MMAM/PM' to minutes since midnight."""
    if 'AM' in t:
        t = t.replace('AM', '').strip()
        hour, minute = map(int, t.split(':'))
        if hour == 12:
            hour = 0
        return hour * 60 + minute
    elif 'PM' in t:
        t = t.replace('PM', '').strip()
        hour, minute = map(int, t.split(':'))
        if hour != 12:
            hour += 12
        return hour * 60 + minute
    else:
        # Already in 24h format H:MM
        hour, minute = map(int, t.split(':'))
        return hour * 60 + minute

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24-hour format."""
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times matrix (minutes)
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Golden Gate Park"): 17,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Golden Gate Park"): 22,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Golden Gate Park"): 22,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
}

# Friends data: name, location, window_start, window_end, min_duration (minutes)
friends = [
    ("Elizabeth", "Mission District", time_to_minutes("10:30AM"), time_to_minutes("8:00PM"), 90),
    ("David", "Union Square", time_to_minutes("3:15PM"), time_to_minutes("7:00PM"), 45),
    ("Sandra", "Pacific Heights", time_to_minutes("7:00AM"), time_to_minutes("8:00PM"), 120),
    ("Thomas", "Bayview", time_to_minutes("7:30PM"), time_to_minutes("8:30PM"), 30),
    ("Robert", "Fisherman's Wharf", time_to_minutes("10:00AM"), time_to_minutes("3:00PM"), 15),
    ("Kenneth", "Marina District", time_to_minutes("10:45AM"), time_to_minutes("1:00PM"), 45),
    ("Melissa", "Richmond District", time_to_minutes("6:15PM"), time_to_minutes("8:00PM"), 15),
    ("Kimberly", "Sunset District", time_to_minutes("10:15AM"), time_to_minutes("6:15PM"), 105),
    ("Amanda", "Golden Gate Park", time_to_minutes("7:45AM"), time_to_minutes("6:45PM"), 15),
]

def schedule_for_permutation(perm):
    """Given a permutation of friends, return (possible, itinerary, meetings_count, total_duration)."""
    current_location = "Haight-Ashbury"
    current_time = time_to_minutes("9:00AM")
    itinerary = []
    meetings_count = 0
    total_duration = 0
    
    for name, loc, win_start, win_end, min_dur in perm:
        travel = travel_times[(current_location, loc)]
        arrive = current_time + travel
        if arrive > win_end:
            return False, None, 0, 0
        start_meeting = max(arrive, win_start)
        if start_meeting + min_dur > win_end:
            return False, None, 0, 0
        end_meeting = start_meeting + min_dur
        itinerary.append((name, loc, start_meeting, end_meeting))
        meetings_count += 1
        total_duration += min_dur
        current_location = loc
        current_time = end_meeting
    return True, itinerary, meetings_count, total_duration

def main():
    best_meetings = 0
    best_duration = 0
    best_itinerary = None
    best_perm = None
    
    # Try all permutations of all friends
    for perm in itertools.permutations(friends):
        possible, itinerary, meetings_count, total_duration = schedule_for_permutation(perm)
        if possible:
            if meetings_count > best_meetings or (meetings_count == best_meetings and total_duration > best_duration):
                best_meetings = meetings_count
                best_duration = total_duration
                best_itinerary = itinerary
                best_perm = perm
    
    # Convert best itinerary to required JSON format
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