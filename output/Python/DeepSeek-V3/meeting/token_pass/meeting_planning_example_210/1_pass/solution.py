import json
import itertools
from datetime import datetime, timedelta

def time_to_minutes(timestr):
    """Convert 'H:MMAM' or 'H:MMPM' to minutes since midnight."""
    if timestr.endswith("AM") or timestr.endswith("PM"):
        dt = datetime.strptime(timestr, "%I:%M%p")
    else:
        dt = datetime.strptime(timestr, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24-hour format."""
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times in minutes: from[to] = time
    travel = {
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Richmond District": 18,
            "Financial District": 11
        },
        "Presidio": {
            "Fisherman's Wharf": 19,
            "Richmond District": 7,
            "Financial District": 23
        },
        "Richmond District": {
            "Fisherman's Wharf": 18,
            "Presidio": 7,
            "Financial District": 22
        },
        "Financial District": {
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Richmond District": 21
        }
    }
    
    # Friend data: name -> (location, window_start, window_end, min_duration)
    friends = {
        "Emily": ("Presidio", time_to_minutes("4:15PM"), time_to_minutes("9:00PM"), 105),
        "Joseph": ("Richmond District", time_to_minutes("5:15PM"), time_to_minutes("10:00PM"), 120),
        "Melissa": ("Financial District", time_to_minutes("3:45PM"), time_to_minutes("9:45PM"), 75)
    }
    
    start_location = "Fisherman's Wharf"
    start_time = time_to_minutes("9:00AM")
    
    best_schedule = []
    max_met = 0
    
    # Try all permutations of all three friends
    for perm in itertools.permutations(friends.keys()):
        current_loc = start_location
        current_time = start_time
        schedule = []
        possible = True
        
        for person in perm:
            loc, win_start, win_end, min_dur = friends[person]
            # Travel to this friend
            travel_time = travel[current_loc][loc]
            arrival = current_time + travel_time
            # Start meeting at max(arrival, window_start)
            meet_start = max(arrival, win_start)
            if meet_start + min_dur > win_end:
                possible = False
                break
            meet_end = meet_start + min_dur
            schedule.append((person, loc, meet_start, meet_end))
            current_loc = loc
            current_time = meet_end
        
        if possible and len(schedule) == 3:
            # Found a full schedule
            best_schedule = schedule
            max_met = 3
            break
    
    # If no full schedule, try subsets of 2 friends
    if max_met < 3:
        for subset in itertools.combinations(friends.keys(), 2):
            for perm in itertools.permutations(subset):
                current_loc = start_location
                current_time = start_time
                schedule = []
                possible = True
                
                for person in perm:
                    loc, win_start, win_end, min_dur = friends[person]
                    travel_time = travel[current_loc][loc]
                    arrival = current_time + travel_time
                    meet_start = max(arrival, win_start)
                    if meet_start + min_dur > win_end:
                        possible = False
                        break
                    meet_end = meet_start + min_dur
                    schedule.append((person, loc, meet_start, meet_end))
                    current_loc = loc
                    current_time = meet_end
                
                if possible and len(schedule) > max_met:
                    max_met = len(schedule)
                    best_schedule = schedule
                    # Keep looking in case another subset also meets 2 but earlier finish
    
    # If still none, try each single friend (should always be possible for at least one)
    if max_met == 0:
        for person in friends.keys():
            loc, win_start, win_end, min_dur = friends[person]
            travel_time = travel[start_location][loc]
            arrival = start_time + travel_time
            meet_start = max(arrival, win_start)
            if meet_start + min_dur <= win_end:
                meet_end = meet_start + min_dur
                best_schedule = [(person, loc, meet_start, meet_end)]
                max_met = 1
                break
    
    # Format output
    itinerary = []
    for person, loc, meet_start, meet_end in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()