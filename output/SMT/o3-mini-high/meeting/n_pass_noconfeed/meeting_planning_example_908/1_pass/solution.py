from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Meeting parameters: times expressed in minutes from midnight.
    # For example, 9:00 AM is 540, 10:00 AM is 600.
    # Each meeting has: name, location, availability window, and minimum meeting duration.
    meetings = [
        {"name": "Mark", "location": "Fisherman's Wharf", "avail_start": 495, "avail_end": 600, "min_duration": 30},
        {"name": "Stephanie", "location": "Presidio", "avail_start": 735, "avail_end": 900, "min_duration": 75},
        {"name": "Betty", "location": "Bayview", "avail_start": 435, "avail_end": 1230, "min_duration": 15},
        {"name": "Lisa", "location": "Haight-Ashbury", "avail_start": 930, "avail_end": 1110, "min_duration": 45},
        {"name": "William", "location": "Russian Hill", "avail_start": 1125, "avail_end": 1200, "min_duration": 60},
        {"name": "Brian", "location": "The Castro", "avail_start": 555, "avail_end": 795, "min_duration": 30},
        {"name": "Joseph", "location": "Marina District", "avail_start": 645, "avail_end": 900, "min_duration": 90},
        {"name": "Ashley", "location": "Richmond District", "avail_start": 585, "avail_end": 675, "min_duration": 45},
        {"name": "Patricia", "location": "Union Square", "avail_start": 990, "avail_end": 1200, "min_duration": 120},
        {"name": "Karen", "location": "Sunset District", "avail_start": 990, "avail_end": 1320, "min_duration": 105}
    ]

    # Travel times (in minutes) between locations.
    travel_times = {
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,

        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,

        ("Presidio", "Financial District"): 23,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,

        ("Bayview", "Financial District"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Sunset District"): 23,

        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,

        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Sunset District"): 23,

        ("The Castro", "Financial District"): 21,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Sunset District"): 17,

        ("Marina District", "Financial District"): 17,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,

        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Sunset District"): 11,

        ("Union Square", "Financial District"): 9,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Sunset District"): 27,

        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Union Square"): 30,
    }

    n = len(meetings)
    # Create an Optimize object so that we can maximize the number of meetings scheduled.
    opt = Optimize()

    # s_vars[i] will represent the meeting start time (in minutes) for meeting i.
    s_vars = [Int(f"s_{i}") for i in range(n)]
    # chosen[i] is True if meeting i is scheduled.
    chosen = [Bool(f"chosen_{i}") for i in range(n)]

    # Add constraints for each meeting.
    for i, meeting in enumerate(meetings):
        avail_start = meeting["avail_start"]
        avail_end = meeting["avail_end"]
        duration = meeting["min_duration"]
        loc = meeting["location"]
        # Meeting must occur within the friend's availability.
        opt.add(Implies(chosen[i], s_vars[i] >= avail_start))
        opt.add(Implies(chosen[i], s_vars[i] + duration <= avail_end))
        # The meeting must be reachable from the Financial District (arrival time is 9:00 which is 540).
        # That is, if meeting i is to be visited directly from the Financial District, 
        # then s_i must be at least 540 + travel time from "Financial District" to its location.
        travel_from_start = travel_times[("Financial District", loc)]
        opt.add(Implies(chosen[i], s_vars[i] >= 540 + travel_from_start))

    # Add disjunctive (non-overlap) constraints for any two meetings scheduled.
    # If both meeting i and meeting j are chosen then either i must come before j or vice-versa,
    # accounting for their minimum durations and travel times.
    for i in range(n):
        for j in range(i+1, n):
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            duration_i = meetings[i]["min_duration"]
            duration_j = meetings[j]["min_duration"]
            travel_ij = travel_times[(loc_i, loc_j)]
            travel_ji = travel_times[(loc_j, loc_i)]
            opt.add(Implies(And(chosen[i], chosen[j]),
                    Or(s_vars[i] + duration_i + travel_ij <= s_vars[j],
                       s_vars[j] + duration_j + travel_ji <= s_vars[i])))

    # Objective: maximize the total number of meetings chosen.
    opt.maximize(Sum([If(chosen[i], 1, 0) for i in range(n)]))

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(chosen[i])):
                start = model.evaluate(s_vars[i]).as_long()
                scheduled.append((start, meetings[i]))
        # Sort meetings in chronological order.
        scheduled.sort(key=lambda x: x[0])
        for start, m in scheduled:
            end = start + m["min_duration"]
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}

    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()