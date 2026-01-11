import itertools
import json

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

# Travel times matrix (directed)
travel = {
    "Bayview": {"Pacific Heights": 23, "Mission District": 13, "Haight-Ashbury": 19, "Financial District": 19},
    "Pacific Heights": {"Bayview": 22, "Mission District": 15, "Haight-Ashbury": 11, "Financial District": 13},
    "Mission District": {"Bayview": 15, "Pacific Heights": 16, "Haight-Ashbury": 12, "Financial District": 17},
    "Haight-Ashbury": {"Bayview": 18, "Pacific Heights": 12, "Mission District": 11, "Financial District": 21},
    "Financial District": {"Bayview": 19, "Pacific Heights": 13, "Mission District": 17, "Haight-Ashbury": 19}
}

# People data: name: (location, start_available, end_available, min_duration_minutes)
people = {
    "Mary": ("Pacific Heights", time_to_minutes("10:00"), time_to_minutes("19:00"), 45),
    "Lisa": ("Mission District", time_to_minutes("20:30"), time_to_minutes("22:00"), 75),
    "Betty": ("Haight-Ashbury", time_to_minutes("7:15"), time_to_minutes("17:15"), 90),
    "Charles": ("Financial District", time_to_minutes("11:15"), time_to_minutes("15:00"), 120)
}

def schedule_meetings(order):
    """
    Given an ordered list of person names, try to schedule them.
    Returns (success, itinerary_list, total_meetings)
    """
    current_location = "Bayview"
    current_time = time_to_minutes("9:00")
    itinerary = []
    
    for person in order:
        loc, start_avail, end_avail, dur = people[person]
        # Travel to loc
        travel_time = travel[current_location][loc]
        arrive_time = current_time + travel_time
        # Start meeting at max(arrive_time, start_avail)
        meet_start = max(arrive_time, start_avail)
        meet_end = meet_start + dur
        # Check if feasible
        if meet_end > end_avail:
            return False, [], 0
        # Add to itinerary
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        # Update current time and location
        current_time = meet_end
        current_location = loc
    
    return True, itinerary, len(order)

def main():
    best_count = 0
    best_itinerary = []
    
    # Try all subsets of people (size 4 down to 1)
    all_people = list(people.keys())
    for r in range(len(all_people), 0, -1):
        for subset in itertools.combinations(all_people, r):
            for perm in itertools.permutations(subset):
                feasible, itinerary, count = schedule_meetings(perm)
                if feasible and count > best_count:
                    best_count = count
                    best_itinerary = itinerary
        # If we found a feasible schedule with r people, we can stop
        # because we want to maximize number of meetings.
        if best_count == r and best_count > 0:
            break
    
    # Output as JSON
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()