import json
import itertools

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes between locations (as provided)
    travel_times = {
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,

        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Marina District"): 17,

        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Marina District"): 11,

        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,

        ("North Beach", "Presidio"): 17,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,

        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Marina District"): 12,

        ("Union Square", "Presidio"): 24,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Marina District"): 18,

        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,

        ("Financial District", "Presidio"): 22,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Marina District"): 15,

        ("Marina District", "Presidio"): 10,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17
    }

    # Friend meeting constraints
    # Times are converted to minutes from midnight.
    # 9:00 AM = 540
    friends = [
        {"name": "Karen", "location": "Haight-Ashbury", "avail_start": 21 * 60, "avail_end": 21 * 60 + 45, "min_meet": 45},
        {"name": "Jessica", "location": "Nob Hill", "avail_start": 13 * 60 + 45, "avail_end": 21 * 60, "min_meet": 90},
        {"name": "Brian", "location": "Russian Hill", "avail_start": 15 * 60 + 30, "avail_end": 21 * 60 + 45, "min_meet": 60},
        {"name": "Kenneth", "location": "North Beach", "avail_start": 9 * 60 + 45, "avail_end": 21 * 60, "min_meet": 30},
        {"name": "Jason", "location": "Chinatown", "avail_start": 8 * 60 + 15, "avail_end": 11 * 60 + 45, "min_meet": 75},
        {"name": "Stephanie", "location": "Union Square", "avail_start": 14 * 60 + 45, "avail_end": 18 * 60 + 45, "min_meet": 105},
        {"name": "Kimberly", "location": "Embarcadero", "avail_start": 9 * 60 + 45, "avail_end": 19 * 60 + 30, "min_meet": 75},
        {"name": "Steven", "location": "Financial District", "avail_start": 7 * 60 + 15, "avail_end": 21 * 60 + 15, "min_meet": 60},
        {"name": "Mark", "location": "Marina District", "avail_start": 10 * 60 + 15, "avail_end": 13 * 60, "min_meet": 75}
    ]

    # Starting point: Presidio at 9:00 AM (540 minutes)
    start_time = 9 * 60

    best_schedule = None
    best_meetings = 0
    best_final_time = float('inf')
    
    # Try every permutation of friend meetings to maximize the count (and then minimize finish time)
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = "Presidio"
        itinerary = []
        feasible = True

        for friend in perm:
            travel = travel_times.get((current_location, friend["location"]))
            if travel is None:
                feasible = False
                break

            arrival_time = current_time + travel
            # Start the meeting when you arrive or when the friend becomes available, whichever is later
            meeting_start = max(arrival_time, friend["avail_start"])
            meeting_end = meeting_start + friend["min_meet"]

            # If meeting cannot be completed before the friend leaves, break this permutation
            if meeting_end > friend["avail_end"]:
                feasible = False
                break

            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            })

            current_time = meeting_end
            current_location = friend["location"]

        if feasible:
            meetings = len(itinerary)
            # Prefer schedules that meet more people and finish earlier
            if meetings > best_meetings or (meetings == best_meetings and current_time < best_final_time):
                best_meetings = meetings
                best_final_time = current_time
                best_schedule = itinerary
            # If you manage to schedule all meetings, you have reached the optimum so exit early.
            if best_meetings == len(friends):
                break

    output = {"itinerary": best_schedule if best_schedule is not None else []}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()