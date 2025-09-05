from z3 import *
import json

def minutes_to_time(minutes):
    # Convert minutes from 9:00 (i.e. 9:00 corresponds to 0) into 24-hour time string "H:MM"
    total = 540 + minutes  # 9:00 is 540 minutes after midnight
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    # Meeting data: each friend has a location, availability window (in minutes after 9:00),
    # and the minimum required meeting duration.
    meetings = [
        {"name": "Kimberly", "location": "Presidio", "window_start": 390, "window_end": 420, "duration": 15},
        {"name": "Elizabeth", "location": "Alamo Square", "window_start": 615, "window_end": 675, "duration": 15},
        {"name": "Joshua", "location": "Marina District", "window_start": 90, "window_end": 315, "duration": 45},
        {"name": "Sandra", "location": "Financial District", "window_start": 630, "window_end": 675, "duration": 45},
        {"name": "Kenneth", "location": "Nob Hill", "window_start": 225, "window_end": 765, "duration": 30},
        {"name": "Betty", "location": "Sunset District", "window_start": 300, "window_end": 600, "duration": 60},
        {"name": "Deborah", "location": "Chinatown", "window_start": 495, "window_end": 690, "duration": 15},
        {"name": "Barbara", "location": "Russian Hill", "window_start": 510, "window_end": 735, "duration": 120},
        {"name": "Steven", "location": "North Beach", "window_start": 525, "window_end": 705, "duration": 90},
        {"name": "Daniel", "location": "Haight-Ashbury", "window_start": 570, "window_end": 585, "duration": 15}
    ]

    # Travel times (in minutes) between San Francisco locations.
    # Keys are origin locations and values are dicts mapping destination locations to travel time.
    travel = {
        "Union Square": {
            "Presidio": 24,
            "Alamo Square": 15,
            "Marina District": 18,
            "Financial District": 9,
            "Nob Hill": 9,
            "Sunset District": 27,
            "Chinatown": 7,
            "Russian Hill": 13,
            "North Beach": 10,
            "Haight-Ashbury": 18
        },
        "Presidio": {
            "Union Square": 22,
            "Alamo Square": 19,
            "Marina District": 11,
            "Financial District": 23,
            "Nob Hill": 18,
            "Sunset District": 15,
            "Chinatown": 21,
            "Russian Hill": 14,
            "North Beach": 18,
            "Haight-Ashbury": 15
        },
        "Alamo Square": {
            "Union Square": 14,
            "Presidio": 17,
            "Marina District": 15,
            "Financial District": 17,
            "Nob Hill": 11,
            "Sunset District": 16,
            "Chinatown": 15,
            "Russian Hill": 13,
            "North Beach": 15,
            "Haight-Ashbury": 5
        },
        "Marina District": {
            "Union Square": 16,
            "Presidio": 10,
            "Alamo Square": 15,
            "Financial District": 17,
            "Nob Hill": 12,
            "Sunset District": 19,
            "Chinatown": 15,
            "Russian Hill": 8,
            "North Beach": 11,
            "Haight-Ashbury": 16
        },
        "Financial District": {
            "Union Square": 9,
            "Presidio": 22,
            "Alamo Square": 17,
            "Marina District": 15,
            "Nob Hill": 8,
            "Sunset District": 30,
            "Chinatown": 5,
            "Russian Hill": 11,
            "North Beach": 7,
            "Haight-Ashbury": 19
        },
        "Nob Hill": {
            "Union Square": 7,
            "Presidio": 17,
            "Alamo Square": 11,
            "Marina District": 11,
            "Financial District": 9,
            "Sunset District": 24,
            "Chinatown": 6,
            "Russian Hill": 5,
            "North Beach": 8,
            "Haight-Ashbury": 13
        },
        "Sunset District": {
            "Union Square": 30,
            "Presidio": 16,
            "Alamo Square": 17,
            "Marina District": 21,
            "Financial District": 30,
            "Nob Hill": 27,
            "Chinatown": 30,
            "Russian Hill": 24,
            "North Beach": 28,
            "Haight-Ashbury": 15
        },
        "Chinatown": {
            "Union Square": 7,
            "Presidio": 19,
            "Alamo Square": 17,
            "Marina District": 12,
            "Financial District": 5,
            "Nob Hill": 9,
            "Sunset District": 29,
            "Russian Hill": 7,
            "North Beach": 3,
            "Haight-Ashbury": 19
        },
        "Russian Hill": {
            "Union Square": 10,
            "Presidio": 14,
            "Alamo Square": 15,
            "Marina District": 7,
            "Financial District": 11,
            "Nob Hill": 5,
            "Sunset District": 23,
            "Chinatown": 9,
            "North Beach": 5,
            "Haight-Ashbury": 17
        },
        "North Beach": {
            "Union Square": 7,
            "Presidio": 17,
            "Alamo Square": 16,
            "Marina District": 9,
            "Financial District": 8,
            "Nob Hill": 7,
            "Sunset District": 27,
            "Chinatown": 6,
            "Russian Hill": 4,
            "Haight-Ashbury": 18
        },
        "Haight-Ashbury": {
            "Union Square": 19,
            "Presidio": 15,
            "Alamo Square": 5,
            "Marina District": 17,
            "Financial District": 21,
            "Nob Hill": 15,
            "Sunset District": 15,
            "Chinatown": 19,
            "Russian Hill": 17,
            "North Beach": 19
        }
    }

    opt = Optimize()
    num_meetings = len(meetings)
    
    # Decision variables:
    # chosen[i] is True if meeting i is scheduled.
    # start_times[i] is the start time (in minutes after 9:00) for meeting i.
    chosen = [Bool(f"chosen_{i}") for i in range(num_meetings)]
    start_times = [Int(f"start_{i}") for i in range(num_meetings)]
    durations = [meeting["duration"] for meeting in meetings]
    
    # If a meeting is chosen, its start time must lie within its availability window (and allow for the meeting duration)
    # and must be no earlier than the travel time needed from Union Square (the starting point).
    for i, meeting in enumerate(meetings):
        win_start = meeting["window_start"]
        win_end = meeting["window_end"]
        dur = meeting["duration"]
        loc = meeting["location"]
        opt.add(Implies(chosen[i],
                        And(start_times[i] >= win_start,
                            start_times[i] + dur <= win_end,
                            start_times[i] >= travel["Union Square"][loc]
                        )))
    
    # Add disjunctive (non-overlap) constraints for every pair of meetings if both are chosen.
    # For any two meetings, either one must finish (including travel time to the other meeting's location)
    # before the other starts.
    for i in range(num_meetings):
        for j in range(i+1, num_meetings):
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            travel_ij = travel[loc_i][loc_j]
            travel_ji = travel[loc_j][loc_i]
            dur_i = durations[i]
            dur_j = durations[j]
            opt.add(Implies(And(chosen[i], chosen[j]),
                        Or(start_times[i] + dur_i + travel_ij <= start_times[j],
                           start_times[j] + dur_j + travel_ji <= start_times[i])))
    
    # Objective: maximize the number of meetings scheduled.
    opt.maximize(Sum([If(ch, 1, 0) for ch in chosen]))
    
    # Solve and construct the schedule from the model.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i, meeting in enumerate(meetings):
            if is_true(model.evaluate(chosen[i])):
                s_time = model.evaluate(start_times[i]).as_long()
                e_time = s_time + meeting["duration"]
                scheduled.append((s_time, {
                    "action": "meet",
                    "location": meeting["location"],
                    "person": meeting["name"],
                    "start_time": minutes_to_time(s_time),
                    "end_time": minutes_to_time(e_time)
                }))
        # Sort scheduled meetings by start time for the itinerary order.
        scheduled.sort(key=lambda x: x[0])
        itinerary = [item[1] for item in scheduled]
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()