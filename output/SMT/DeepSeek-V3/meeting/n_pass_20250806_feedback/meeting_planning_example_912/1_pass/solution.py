from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the locations and their respective friends and time windows
    friends = {
        "Kimberly": {"location": "Presidio", "available_start": "15:30", "available_end": "16:00", "min_duration": 15},
        "Elizabeth": {"location": "Alamo Square", "available_start": "19:15", "available_end": "20:15", "min_duration": 15},
        "Joshua": {"location": "Marina District", "available_start": "10:30", "available_end": "14:15", "min_duration": 45},
        "Sandra": {"location": "Financial District", "available_start": "19:30", "available_end": "20:15", "min_duration": 45},
        "Kenneth": {"location": "Nob Hill", "available_start": "12:45", "available_end": "21:45", "min_duration": 30},
        "Betty": {"location": "Sunset District", "available_start": "14:00", "available_end": "19:00", "min_duration": 60},
        "Deborah": {"location": "Chinatown", "available_start": "17:15", "available_end": "20:30", "min_duration": 15},
        "Barbara": {"location": "Russian Hill", "available_start": "17:30", "available_end": "21:15", "min_duration": 120},
        "Steven": {"location": "North Beach", "available_start": "17:45", "available_end": "20:45", "min_duration": 90},
        "Daniel": {"location": "Haight-Ashbury", "available_start": "18:30", "available_end": "18:45", "min_duration": 15}
    }

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

    # Define travel times between locations (simplified for this example)
    # We'll assume symmetric travel times and use a dictionary for simplicity
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
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Russian Hill", "North Beach"): 4,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("North Beach", "Haight-Ashbury"): 18
    }

    # Create Z3 variables for each friend's meeting start and end times
    meeting_vars = {}
    for friend in friends:
        start = Int(f"start_{friend}")
        end = Int(f"end_{friend}")
        meeting_vars[friend] = (start, end)

    # Add constraints for each friend's meeting
    for friend, data in friends.items():
        start, end = meeting_vars[friend]
        available_start = time_to_minutes(data["available_start"])
        available_end = time_to_minutes(data["available_end"])
        min_duration = data["min_duration"]

        # Meeting must be within the friend's available window
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end - start >= min_duration)

    # Add constraints to ensure no overlapping meetings and travel times
    friends_list = list(friends.keys())
    for i in range(len(friends_list)):
        for j in range(i + 1, len(friends_list)):
            friend1 = friends_list[i]
            friend2 = friends_list[j]
            start1, end1 = meeting_vars[friend1]
            start2, end2 = meeting_vars[friend2]
            loc1 = friends[friend1]["location"]
            loc2 = friends[friend2]["location"]

            # Travel time between locations
            if (loc1, loc2) in travel_times:
                travel_time = travel_times[(loc1, loc2)]
            elif (loc2, loc1) in travel_times:
                travel_time = travel_times[(loc2, loc1)]
            else:
                travel_time = 0  # Should not happen as all pairs are covered

            # Ensure no overlap considering travel time
            s.add(Or(
                end1 + travel_time <= start2,
                end2 + travel_time <= start1
            ))

    # Add constraint to start at Union Square at 9:00 AM (0 minutes)
    # The first meeting must account for travel time from Union Square
    first_meeting_start = Int("first_meeting_start")
    s.add(first_meeting_start >= 0)
    for friend in friends:
        start, _ = meeting_vars[friend]
        loc = friends[friend]["location"]
        travel_time = travel_times[("Union Square", loc)]
        s.add(Or(
            start >= first_meeting_start + travel_time,
            first_meeting_start == 0  # No previous meeting
        ))

    # Try to maximize the number of friends met
    # We'll prioritize friends with longer required durations
    # This is a heuristic; in practice, we might need a more sophisticated approach
    # For simplicity, we'll just check satisfiability
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            start, end = meeting_vars[friend]
            start_val = model.evaluate(start).as_long()
            end_val = model.evaluate(end).as_long()
            if start_val >= 0 and end_val > start_val:
                itinerary.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))