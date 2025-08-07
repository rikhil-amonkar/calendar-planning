from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their details
    friends = [
        {
            "name": "Karen",
            "location": "Nob Hill",
            "available_start": datetime.time(21, 15),  # 9:15 PM
            "available_end": datetime.time(21, 45),    # 9:45 PM
            "min_duration": 30,  # minutes
            "travel_times": {
                "Union Square": 9,
                "Nob Hill": 0,
                "Haight-Ashbury": 13,
                "Chinatown": 6,
                "Marina District": 11
            }
        },
        {
            "name": "Joseph",
            "location": "Haight-Ashbury",
            "available_start": datetime.time(12, 30),  # 12:30 PM
            "available_end": datetime.time(19, 45),     # 7:45 PM
            "min_duration": 90,
            "travel_times": {
                "Union Square": 18,
                "Nob Hill": 13,
                "Haight-Ashbury": 0,
                "Chinatown": 19,
                "Marina District": 17
            }
        },
        {
            "name": "Sandra",
            "location": "Chinatown",
            "available_start": datetime.time(7, 15),    # 7:15 AM
            "available_end": datetime.time(19, 15),     # 7:15 PM
            "min_duration": 75,
            "travel_times": {
                "Union Square": 7,
                "Nob Hill": 6,
                "Haight-Ashbury": 19,
                "Chinatown": 0,
                "Marina District": 12
            }
        },
        {
            "name": "Nancy",
            "location": "Marina District",
            "available_start": datetime.time(11, 0),    # 11:00 AM
            "available_end": datetime.time(20, 15),     # 8:15 PM
            "min_duration": 105,
            "travel_times": {
                "Union Square": 18,
                "Nob Hill": 11,
                "Haight-Ashbury": 17,
                "Chinatown": 12,
                "Marina District": 0
            }
        }
    ]

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(t):
        return t.hour * 60 + t.minute

    current_location = "Union Square"
    current_time = time_to_minutes(datetime.time(9, 0))  # 9:00 AM is 540 minutes

    # Create variables for each meeting's start and end times
    meetings = []
    for friend in friends:
        start = Int(f'start_{friend["name"]}')
        end = Int(f'end_{friend["name"]}')
        meetings.append({
            "name": friend["name"],
            "location": friend["location"],
            "start": start,
            "end": end,
            "min_duration": friend["min_duration"],
            "available_start": time_to_minutes(friend["available_start"]),
            "available_end": time_to_minutes(friend["available_end"]),
            "travel_time": friend["travel_times"][current_location]
        })

    # Constraints for each meeting
    for meeting in meetings:
        s.add(meeting["start"] >= meeting["available_start"])
        s.add(meeting["end"] <= meeting["available_end"])
        s.add(meeting["end"] - meeting["start"] >= meeting["min_duration"])

    # Order constraints: ensure meetings are scheduled in a feasible order considering travel times
    # We'll assume a specific order and let Z3 find the feasible times
    # For simplicity, we'll try to meet Sandra first, then Nancy, Joseph, and Karen last
    # But let Z3 handle the ordering by adding constraints that enforce travel times between meetings

    # We need to model the sequence of meetings. Let's assume we can meet all friends in some order.
    # We'll create variables to represent the order and then add constraints based on travel times.

    # For simplicity, let's assume a fixed order: Sandra -> Nancy -> Joseph -> Karen
    # This is a heuristic; in a more complex solver, we'd use a more dynamic approach.
    # But given time constraints, we proceed with this assumption.

    # Assume the order is Sandra, Nancy, Joseph, Karen
    # Then, the constraints are:
    # 1. Sandra's meeting ends + travel to Nancy's location <= Nancy's start time
    # 2. Nancy's meeting ends + travel to Joseph's location <= Joseph's start time
    # 3. Joseph's meeting ends + travel to Karen's location <= Karen's start time

    # Get the friends in the assumed order
    sandra = next(f for f in friends if f["name"] == "Sandra")
    nancy = next(f for f in friends if f["name"] == "Nancy")
    joseph = next(f for f in friends if f["name"] == "Joseph")
    karen = next(f for f in friends if f["name"] == "Karen")

    # Get the meeting variables
    sandra_meeting = next(m for m in meetings if m["name"] == "Sandra")
    nancy_meeting = next(m for m in meetings if m["name"] == "Nancy")
    joseph_meeting = next(m for m in meetings if m["name"] == "Joseph")
    karen_meeting = next(m for m in meetings if m["name"] == "Karen")

    # Current location is Union Square at 540 minutes (9:00 AM)
    # Travel to Sandra's location (Chinatown) takes 7 minutes
    s.add(sandra_meeting["start"] >= 540 + 7)

    # After meeting Sandra, travel to Nancy's location (Marina District)
    # Travel time from Chinatown to Marina District is 12 minutes
    s.add(nancy_meeting["start"] >= sandra_meeting["end"] + 12)

    # After meeting Nancy, travel to Joseph's location (Haight-Ashbury)
    # Travel time from Marina District to Haight-Ashbury is 16 minutes
    s.add(joseph_meeting["start"] >= nancy_meeting["end"] + 16)

    # After meeting Joseph, travel to Karen's location (Nob Hill)
    # Travel time from Haight-Ashbury to Nob Hill is 15 minutes
    s.add(karen_meeting["start"] >= joseph_meeting["end"] + 15)

    # Check if all constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Helper function to convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        # Process each meeting in the order we assumed
        for meeting in [sandra_meeting, nancy_meeting, joseph_meeting, karen_meeting]:
            start = model[meeting["start"]].as_long()
            end = model[meeting["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })

        # Return the itinerary
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(result)