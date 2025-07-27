from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define the locations and their travel times
    locations = [
        "Embarcadero", "Fisherman's Wharf", "Financial District", "Russian Hill", "Marina District",
        "Richmond District", "Pacific Heights", "Haight-Ashbury", "Presidio", "Nob Hill", "The Castro"
    ]

    # Travel times in minutes between locations (symmetric)
    travel_times = {
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "The Castro"): 20,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "The Castro"): 21,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "The Castro"): 22,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "The Castro"): 16,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "The Castro"): 16,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "The Castro"): 21,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "The Castro"): 16,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Nob Hill"): 16,
    }

    # Friends and their constraints
    friends = [
        {"name": "Stephanie", "location": "Fisherman's Wharf", "start": "15:30", "end": "22:00", "duration": 30},
        {"name": "Lisa", "location": "Financial District", "start": "10:45", "end": "17:15", "duration": 15},
        {"name": "Melissa", "location": "Russian Hill", "start": "17:00", "end": "21:45", "duration": 120},
        {"name": "Betty", "location": "Marina District", "start": "10:45", "end": "14:15", "duration": 60},
        {"name": "Sarah", "location": "Richmond District", "start": "16:15", "end": "19:30", "duration": 105},
        {"name": "Daniel", "location": "Pacific Heights", "start": "18:30", "end": "21:45", "duration": 60},
        {"name": "Joshua", "location": "Haight-Ashbury", "start": "09:00", "end": "15:30", "duration": 15},
        {"name": "Joseph", "location": "Presidio", "start": "07:00", "end": "13:00", "duration": 45},
        {"name": "Andrew", "location": "Nob Hill", "start": "19:45", "end": "22:00", "duration": 105},
        {"name": "John", "location": "The Castro", "start": "13:15", "end": "19:45", "duration": 45},
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each friend's meeting start and end times
    meeting_vars = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend['duration']
        meeting_vars.append((friend, start, end))

        # Constraints: start and end within friend's availability
        opt.add(start >= time_to_minutes(friend['start']))
        opt.add(end <= time_to_minutes(friend['end']))
        opt.add(end == start + duration)

    # Add constraints to ensure no overlapping meetings and travel times
    for i in range(len(meeting_vars)):
        for j in range(i + 1, len(meeting_vars)):
            friend1, start1, end1 = meeting_vars[i]
            friend2, start2, end2 = meeting_vars[j]

            # Travel time between locations
            loc1 = friend1['location']
            loc2 = friend2['location']
            travel_time = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))

            # Either meeting1 is before meeting2 with travel time or vice versa
            opt.add(Or(
                end1 + travel_time <= start2,
                end2 + travel_time <= start1
            ))

    # Add constraint to start at Embarcadero at 9:00 AM (0 minutes)
    # The first meeting must be after traveling from Embarcadero
    first_meeting_start = Int("first_meeting_start")
    opt.add(first_meeting_start >= 0)
    for friend, start, _ in meeting_vars:
        loc = friend['location']
        travel_time = travel_times.get(("Embarcadero", loc), travel_times.get((loc, "Embarcadero"), 0))
        opt.add(Or(start >= first_meeting_start + travel_time, start == 0))

    # Maximize the number of friends met (soft constraint)
    # Alternatively, maximize the total meeting time
    total_meeting_time = Int("total_meeting_time")
    opt.add(total_meeting_time == sum([end - start for _, start, end in meeting_vars]))
    opt.maximize(total_meeting_time)

    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for friend, start, end in meeting_vars:
            start_val = m.evaluate(start).as_long()
            end_val = m.evaluate(end).as_long()
            if start_val >= 0 and end_val > start_val:
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the optimizer and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))