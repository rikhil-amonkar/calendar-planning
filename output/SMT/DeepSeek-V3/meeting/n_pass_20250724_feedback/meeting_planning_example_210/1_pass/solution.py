from itertools import permutations

def solve_scheduling():
    # Travel times between locations (in minutes)
    # Locations: Fisherman's Wharf (0), Presidio (1), Richmond (2), Financial (3)
    travel_times = {
        (0, 1): 17, (0, 2): 18, (0, 3): 11,
        (1, 0): 19, (1, 2): 7, (1, 3): 23,
        (2, 0): 18, (2, 1): 7, (2, 3): 22,
        (3, 0): 10, (3, 1): 22, (3, 2): 21
    }

    # Friends' data: name, location, start_avail, end_avail, min_duration
    friends = [
        ("Emily", 1, 15*60+15, 21*60, 105),
        ("Joseph", 2, 17*60+15, 22*60, 120),
        ("Melissa", 3, 15*60+45, 21*60+45, 75)
    ]

    # Current location is Fisherman's Wharf (0) at time 9:00 AM (0 minutes since start)
    current_time = 0
    current_loc = 0

    # Try all possible orders of meeting friends
    for order in permutations(friends):
        schedule = []
        feasible = True
        current_time = 0
        current_loc = 0
        for friend in order:
            name, loc, start_avail, end_avail, duration = friend
            # Travel time to friend's location
            travel_time = travel_times[(current_loc, loc)]
            arrival_time = current_time + travel_time
            # The earliest we can start the meeting is max(arrival_time, start_avail - 9*60)
            meeting_start = max(arrival_time, start_avail - 9*60)
            meeting_end = meeting_start + duration
            if meeting_end > end_avail - 9*60:
                feasible = False
                break
            schedule.append((name, meeting_start, meeting_end))
            current_time = meeting_end
            current_loc = loc
        if feasible:
            # Convert times to HH:MM
            itinerary = []
            for name, start, end in schedule:
                start_hour = 9 + start // 60
                start_min = start % 60
                end_hour = 9 + end // 60
                end_min = end % 60
                start_time = f"{start_hour:02d}:{start_min:02d}"
                end_time = f"{end_hour:02d}:{end_min:02d}"
                itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
            # Sort by start time (though the order should already be correct)
            itinerary.sort(key=lambda x: x["start_time"])
            return {"itinerary": itinerary}
    return {"error": "No feasible schedule found."}

solution = solve_scheduling()
print(solution)