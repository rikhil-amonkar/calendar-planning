from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Stephanie": {"location": "Golden Gate Park", "start": (11, 0), "end": (15, 0), "duration": 105},
        "Karen": {"location": "Chinatown", "start": (13, 45), "end": (16, 30), "duration": 15},
        "Brian": {"location": "Union Square", "start": (15, 0), "end": (17, 15), "duration": 30},
        "Rebecca": {"location": "Fisherman's Wharf", "start": (8, 0), "end": (11, 15), "duration": 30},
        "Joseph": {"location": "Pacific Heights", "start": (8, 15), "end": (9, 30), "duration": 60},
        "Steven": {"location": "North Beach", "start": (14, 30), "end": (20, 45), "duration": 120}
    }

    # Define travel times (from_location, to_location): minutes
    travel_times = {
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "North Beach"): 7,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "North Beach"): 24,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "North Beach"): 3,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "North Beach"): 10,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "North Beach"): 9,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Pacific Heights"): 8,
    }

    # Convert times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(m):
        total = m + 540
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Create variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = {"start": start, "end": end}
        # Add constraints for meeting duration and availability
        s.add(start >= time_to_minutes(*friends[name]["start"]))
        s.add(end <= time_to_minutes(*friends[name]["end"]))
        s.add(end == start + friends[name]["duration"])

    # Define the order of meetings and travel times
    # We need to ensure that the end time of one meeting + travel time <= start time of the next meeting
    # We'll try to meet all friends, so we need to find a permutation that fits

    # Since Z3 doesn't handle permutations directly, we'll define a sequence
    # Here, we'll assume a possible order and let Z3 find the exact times
    # The order is: Joseph, Rebecca, Stephanie, Karen, Steven, Brian
    # This is a heuristic based on their availability windows

    # Joseph (Pacific Heights)
    s.add(meeting_vars["Joseph"]["start"] >= time_to_minutes(8, 15))
    s.add(meeting_vars["Joseph"]["end"] <= time_to_minutes(9, 30))

    # Rebecca (Fisherman's Wharf)
    s.add(meeting_vars["Rebecca"]["start"] >= time_to_minutes(8, 0))
    s.add(meeting_vars["Rebecca"]["end"] <= time_to_minutes(11, 15))
    # Travel from Financial District to Pacific Heights: 13 minutes
    # Since we start at Financial District at 9:00 AM, we can't meet Joseph first (he's only available until 9:30 AM)
    # So we'll meet Rebecca first, then Joseph
    # Wait, no: Joseph is only available from 8:15 AM to 9:30 AM, and we arrive at 9:00 AM
    # So we can meet Joseph from 9:00 AM to 10:00 AM (60 minutes), but his window ends at 9:30 AM
    # So we can only meet Joseph from 9:00 AM to 9:30 AM (30 minutes), but we need 60 minutes
    # So we can't meet Joseph at all? Or is the duration flexible?
    # The problem says "minimum of 60 minutes", but his window is only 75 minutes (8:15 AM to 9:30 AM)
    # And we arrive at 9:00 AM, so we can meet him from 9:00 AM to 9:30 AM (30 minutes)
    # But the minimum is 60 minutes, so we can't meet Joseph. We'll skip him.

    # So the order is: Rebecca, Stephanie, Karen, Steven, Brian

    # Rebecca (Fisherman's Wharf)
    s.add(meeting_vars["Rebecca"]["start"] >= 0)  # 9:00 AM is 0 minutes
    s.add(meeting_vars["Rebecca"]["end"] <= time_to_minutes(11, 15))
    # Travel from Financial District to Fisherman's Wharf: 10 minutes
    # So Rebecca's start time is at least 10 minutes after 9:00 AM (i.e., 9:10 AM)
    s.add(meeting_vars["Rebecca"]["start"] >= 10)

    # Stephanie (Golden Gate Park)
    s.add(meeting_vars["Stephanie"]["start"] >= time_to_minutes(11, 0))
    s.add(meeting_vars["Stephanie"]["end"] <= time_to_minutes(15, 0))
    # Travel from Fisherman's Wharf to Golden Gate Park: 25 minutes
    s.add(meeting_vars["Stephanie"]["start"] >= meeting_vars["Rebecca"]["end"] + 25)

    # Karen (Chinatown)
    s.add(meeting_vars["Karen"]["start"] >= time_to_minutes(13, 45))
    s.add(meeting_vars["Karen"]["end"] <= time_to_minutes(16, 30))
    # Travel from Golden Gate Park to Chinatown: 23 minutes
    s.add(meeting_vars["Karen"]["start"] >= meeting_vars["Stephanie"]["end"] + 23)

    # Steven (North Beach)
    s.add(meeting_vars["Steven"]["start"] >= time_to_minutes(14, 30))
    s.add(meeting_vars["Steven"]["end"] <= time_to_minutes(20, 45))
    # Travel from Chinatown to North Beach: 3 minutes
    s.add(meeting_vars["Steven"]["start"] >= meeting_vars["Karen"]["end"] + 3)

    # Brian (Union Square)
    s.add(meeting_vars["Brian"]["start"] >= time_to_minutes(15, 0))
    s.add(meeting_vars["Brian"]["end"] <= time_to_minutes(17, 15))
    # Travel from North Beach to Union Square: 7 minutes
    s.add(meeting_vars["Brian"]["start"] >= meeting_vars["Steven"]["end"] + 7)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            start = model[meeting_vars[name]["start"]].as_long()
            end = model[meeting_vars[name]["end"]].as_long()
            if start >= 0 and end >= 0:  # Only add meetings that are scheduled
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))