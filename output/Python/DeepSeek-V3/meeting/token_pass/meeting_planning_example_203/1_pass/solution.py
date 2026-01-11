import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times matrix (in minutes)
    travel = {
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Mission District"): 17,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Financial District"): 17,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Pacific Heights"): 16,
    }
    
    # Friend data: name, location, window start, window end, min duration (minutes)
    friends = [
        ("David", "Fisherman's Wharf", time_to_minutes("10:45"), time_to_minutes("15:30"), 15),
        ("Timothy", "Pacific Heights", time_to_minutes("9:00"), time_to_minutes("15:30"), 75),
        ("Robert", "Mission District", time_to_minutes("12:15"), time_to_minutes("19:45"), 90),
    ]
    
    start_location = "Financial District"
    start_time = time_to_minutes("9:00")
    
    best_schedule = None
    best_friends_met = 0
    best_total_time = 0
    
    # Try all permutations of friends
    for perm in itertools.permutations(range(len(friends))):
        current_loc = start_location
        current_time = start_time
        schedule = []
        possible = True
        
        for idx in perm:
            name, loc, win_start, win_end, min_dur = friends[idx]
            # Travel to friend
            travel_time = travel.get((current_loc, loc))
            if travel_time is None:
                # Should not happen given complete matrix
                possible = False
                break
            arrival = current_time + travel_time
            # Start of meeting
            meet_start = max(arrival, win_start)
            if meet_start + min_dur > win_end:
                possible = False
                break
            # We can extend meeting until latest possible
            # Latest end considering next friend? We'll extend greedily for now
            # but must ensure we can meet remaining friends.
            # For simplicity, first schedule min duration, then later extend if possible.
            meet_end = meet_start + min_dur
            schedule.append((name, loc, meet_start, meet_end, min_dur))
            current_time = meet_end
            current_loc = loc
        
        if possible:
            friends_met = len(schedule)
            total_time = sum(end - start for _, _, start, end, _ in schedule)
            # Try to extend meetings if time allows (greedy backward extension)
            # We'll extend each meeting to fill until next travel or window end
            extended_schedule = []
            for i in range(len(schedule)):
                name, loc, start, end, min_dur = schedule[i]
                # Max end time is friend's window end
                max_end = friends[[f[0] for f in friends].index(name)][3]
                if i < len(schedule) - 1:
                    # Also limited by need to travel to next friend
                    next_name, next_loc, next_start, _, _ = schedule[i+1]
                    travel_to_next = travel.get((loc, next_loc))
                    # We must leave by next_start - travel_to_next
                    latest_departure = next_start - travel_to_next
                    max_end = min(max_end, latest_departure)
                # Extend to max_end
                new_end = max_end
                if new_end > end:
                    end = new_end
                extended_schedule.append((name, loc, start, end))
            
            total_time_extended = sum(end - start for _, _, start, end in extended_schedule)
            
            # Evaluate
            if (friends_met > best_friends_met or
                (friends_met == best_friends_met and total_time_extended > best_total_time)):
                best_friends_met = friends_met
                best_total_time = total_time_extended
                best_schedule = extended_schedule
    
    # If best_schedule is None, try 2-friend combinations
    if best_schedule is None or best_friends_met < 3:
        best_schedule = None
        best_friends_met = 0
        best_total_time = 0
        # Try all subsets of size 2
        for perm in itertools.permutations(range(len(friends)), 2):
            current_loc = start_location
            current_time = start_time
            schedule = []
            possible = True
            for idx in perm:
                name, loc, win_start, win_end, min_dur = friends[idx]
                travel_time = travel.get((current_loc, loc))
                if travel_time is None:
                    possible = False
                    break
                arrival = current_time + travel_time
                meet_start = max(arrival, win_start)
                if meet_start + min_dur > win_end:
                    possible = False
                    break
                meet_end = meet_start + min_dur
                schedule.append((name, loc, meet_start, meet_end, min_dur))
                current_time = meet_end
                current_loc = loc
            if possible:
                friends_met = len(schedule)
                total_time = sum(end - start for _, _, start, end, _ in schedule)
                # Extend
                extended_schedule = []
                for i in range(len(schedule)):
                    name, loc, start, end, min_dur = schedule[i]
                    max_end = friends[[f[0] for f in friends].index(name)][3]
                    if i < len(schedule) - 1:
                        next_name, next_loc, next_start, _, _ = schedule[i+1]
                        travel_to_next = travel.get((loc, next_loc))
                        latest_departure = next_start - travel_to_next
                        max_end = min(max_end, latest_departure)
                    new_end = max_end
                    if new_end > end:
                        end = new_end
                    extended_schedule.append((name, loc, start, end))
                total_time_extended = sum(end - start for _, _, start, end in extended_schedule)
                if (friends_met > best_friends_met or
                    (friends_met == best_friends_met and total_time_extended > best_total_time)):
                    best_friends_met = friends_met
                    best_total_time = total_time_extended
                    best_schedule = extended_schedule
    
    # Format output
    itinerary = []
    if best_schedule:
        for name, loc, start, end in best_schedule:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()