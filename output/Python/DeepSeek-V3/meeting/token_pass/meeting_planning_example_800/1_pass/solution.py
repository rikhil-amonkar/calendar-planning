import json
from itertools import permutations
from datetime import datetime, timedelta

# Travel times dictionary
travel_times = {
    ("Union Square", "The Castro"): 17,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Embarcadero"): 11,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Haight-Ashbury"): 18,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Haight-Ashbury"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Haight-Ashbury"): 18,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Presidio"): 17,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Nob Hill"): 18,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
}

# Friend data: name, location, start, end, min_duration (minutes)
friends = [
    ("Melissa", "The Castro", "20:15", "21:15", 30),
    ("Kimberly", "North Beach", "7:00", "10:30", 15),
    ("Joseph", "Embarcadero", "15:30", "19:30", 75),
    ("Barbara", "Alamo Square", "20:45", "21:45", 15),
    ("Kenneth", "Nob Hill", "12:15", "17:15", 105),
    ("Joshua", "Presidio", "16:30", "18:15", 105),
    ("Brian", "Fisherman's Wharf", "9:30", "15:30", 45),
    ("Steven", "Mission District", "19:30", "21:00", 90),
    ("Betty", "Haight-Ashbury", "19:00", "20:30", 90),
]

def parse_time(t):
    return datetime.strptime(t, "%H:%M")

def time_str(t):
    return t.strftime("%H:%M")

def add_minutes(t, minutes):
    return t + timedelta(minutes=minutes)

def can_schedule(order, start_location="Union Square", start_time_str="9:00"):
    current_time = parse_time(start_time_str)
    current_location = start_location
    schedule = []
    for name, location, win_start_str, win_end_str, min_dur in order:
        win_start = parse_time(win_start_str)
        win_end = parse_time(win_end_str)
        # Travel to location
        travel = travel_times.get((current_location, location))
        if travel is None:
            travel = 0  # same location
        arrive_time = add_minutes(current_time, travel)
        # If arrive after window ends, impossible
        if arrive_time > win_end:
            return None
        # Start meeting at max(arrive_time, win_start)
        meet_start = max(arrive_time, win_start)
        # If not enough time before window ends, impossible
        if add_minutes(meet_start, min_dur) > win_end:
            return None
        meet_end = add_minutes(meet_start, min_dur)
        schedule.append((name, location, meet_start, meet_end))
        current_time = meet_end
        current_location = location
    return schedule

def schedule_score(schedule):
    # Number of friends met
    return len(schedule)

def main():
    best_score = -1
    best_schedule = None
    best_order = None
    
    # Try permutations of subsets (but 9! is huge, so we prune)
    # We'll try all permutations of up to all friends (small set, 9! = 362880, manageable)
    from itertools import permutations
    for perm in permutations(friends):
        sched = can_schedule(perm)
        if sched:
            score = schedule_score(sched)
            if score > best_score:
                best_score = score
                best_schedule = sched
                best_order = perm
                if best_score == len(friends):
                    break  # found optimal
    
    # Convert to required JSON format
    itinerary = []
    for name, location, start, end in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": time_str(start),
            "end_time": time_str(end)
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()