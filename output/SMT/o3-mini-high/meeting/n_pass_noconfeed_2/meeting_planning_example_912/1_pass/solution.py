from z3 import *
import json

def convert_time(minutes_after_9):
    # Convert minutes after 9:00 (i.e., 9:00 is 0) to a "H:MM" 24-hour string.
    total = minutes_after_9 + 9 * 60
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times in minutes between locations (non-symmetric)
    travel_times = {
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Haight-Ashbury"): 18,
        
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Haight-Ashbury"): 15,
        
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Haight-Ashbury"): 5,
        
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Haight-Ashbury"): 16,
        
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Haight-Ashbury"): 19,
        
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Haight-Ashbury"): 15,
        
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Haight-Ashbury"): 19,
        
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Haight-Ashbury"): 17,
        
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Haight-Ashbury"): 18,
        
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "North Beach"): 19,
    }

    # Friend meeting constraints with time windows (times are minutes after 9:00)
    # For each friend, we have: name, location, availability window [start, end] and minimum meeting duration.
    friends = [
        {"name": "Kimberly", "location": "Presidio", "avail_start": 390, "avail_end": 420, "min_duration": 15},
        {"name": "Elizabeth", "location": "Alamo Square", "avail_start": 615, "avail_end": 675, "min_duration": 15},
        {"name": "Joshua", "location": "Marina District", "avail_start": 90,  "avail_end": 315, "min_duration": 45},
        {"name": "Sandra", "location": "Financial District", "avail_start": 630, "avail_end": 675, "min_duration": 45},
        {"name": "Kenneth", "location": "Nob Hill", "avail_start": 225, "avail_end": 745, "min_duration": 30},
        {"name": "Betty", "location": "Sunset District", "avail_start": 300, "avail_end": 600, "min_duration": 60},
        {"name": "Deborah", "location": "Chinatown", "avail_start": 495, "avail_end": 690, "min_duration": 15},
        {"name": "Barbara", "location": "Russian Hill", "avail_start": 510, "avail_end": 735, "min_duration": 120},
        {"name": "Steven", "location": "North Beach", "avail_start": 525, "avail_end": 645, "min_duration": 90},
        {"name": "Daniel", "location": "Haight-Ashbury", "avail_start": 570, "avail_end": 585, "min_duration": 15}
    ]
    
    n = len(friends)
    opt = Optimize()
    
    # Decision variables for each friend:
    # scheduled[i] indicates whether to meet friend i.
    scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
    start_times = [Int(f"start_{i}") for i in range(n)]  # meeting start time (minutes after 9:00)
    end_times = [Int(f"end_{i}") for i in range(n)]      # meeting end time (minutes after 9:00)

    # Add constraints for each meeting (if scheduled)
    for i, friend in enumerate(friends):
        avail_start = friend["avail_start"]
        avail_end = friend["avail_end"]
        min_duration = friend["min_duration"]
        # Meeting must start no earlier than the friend’s available start time
        opt.add(Implies(scheduled[i], start_times[i] >= avail_start))
        # Meeting must finish before the friend’s available end time 
        opt.add(Implies(scheduled[i], end_times[i] <= avail_end))
        # Meeting duration must be at least the minimum required
        opt.add(Implies(scheduled[i], end_times[i] - start_times[i] >= min_duration))
        # Must have enough travel time from Union Square (starting point) to the meeting location.
        travel_from_start = travel_times[("Union Square", friend["location"])]
        opt.add(Implies(scheduled[i], start_times[i] >= travel_from_start))
        # Ensure non-negative start and end times
        opt.add(Implies(scheduled[i], start_times[i] >= 0))
        opt.add(Implies(scheduled[i], end_times[i] >= 0))
        # Bound times to a reasonable maximum (e.g., by 800 minutes after 9:00)
        opt.add(Implies(scheduled[i], start_times[i] <= 800))
        opt.add(Implies(scheduled[i], end_times[i] <= 800))
    
    # Add travel constraints between any two scheduled meetings.
    # For any two friends i and j, if both meetings are scheduled, then either
    # meeting i occurs before meeting j (with travel time from i's location to j's)
    # or j occurs before i.
    for i in range(n):
        for j in range(i + 1, n):
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_i_to_j = travel_times[(loc_i, loc_j)]
            travel_j_to_i = travel_times[(loc_j, loc_i)]
            opt.add(Implies(And(scheduled[i], scheduled[j]),
                            Or(end_times[i] + travel_i_to_j <= start_times[j],
                               end_times[j] + travel_j_to_i <= start_times[i])))
    
    # Objective: maximize the number of friends scheduled (i.e., meet as many as possible)
    total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        meetings = []
        for i in range(n):
            if is_true(model.evaluate(scheduled[i])):
                st = model.evaluate(start_times[i]).as_long()
                et = model.evaluate(end_times[i]).as_long()
                meetings.append((st, et, friends[i]["location"], friends[i]["name"]))
        # Sort meetings by start time
        meetings.sort(key=lambda x: x[0])
        for st, et, location, person in meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": convert_time(st),
                "end_time": convert_time(et)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
    
if __name__ == "__main__":
    main()