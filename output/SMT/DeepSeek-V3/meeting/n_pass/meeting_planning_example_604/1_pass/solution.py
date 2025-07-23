from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Laura": {"location": "The Castro", "start": "19:45", "end": "21:30", "min_duration": 105},
        "Daniel": {"location": "Golden Gate Park", "start": "21:15", "end": "21:45", "min_duration": 15},
        "William": {"location": "Embarcadero", "start": "07:00", "end": "09:00", "min_duration": 90},
        "Karen": {"location": "Russian Hill", "start": "14:30", "end": "19:45", "min_duration": 30},
        "Stephanie": {"location": "Nob Hill", "start": "07:30", "end": "09:30", "min_duration": 45},
        "Joseph": {"location": "Alamo Square", "start": "11:30", "end": "12:45", "min_duration": 15},
        "Kimberly": {"location": "North Beach", "start": "15:45", "end": "19:15", "min_duration": 30}
    }

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"{name}_start")
        end_var = Int(f"{name}_end")
        meeting_vars[name] = {"start": start_var, "end": end_var}

    # Current location starts at Fisherman's Wharf at 9:00 AM (540 minutes)
    current_location = "Fisherman's Wharf"
    current_time = 540  # 9:00 AM in minutes

    # Define the travel times dictionary
    travel_times = {
        ("Fisherman's Wharf", "The Castro"): 26,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "North Beach"): 20,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "North Beach"): 24,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "North Beach"): 5,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "North Beach"): 5,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Alamo Square"): 16
    }

    # Constraints for each friend's meeting time
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]

        s.add(meeting_vars[name]["start"] >= start_min)
        s.add(meeting_vars[name]["end"] <= end_min)
        s.add(meeting_vars[name]["end"] - meeting_vars[name]["start"] >= min_duration)

    # Define the order of meetings and travel times
    # We need to sequence the meetings such that travel times are respected
    # This is complex; for simplicity, we'll assume a certain order and check feasibility
    # Alternatively, we can use a more sophisticated approach with additional variables for ordering

    # For the purpose of this example, let's try to meet William first (if possible)
    # But William's window is 7:00-9:00 AM, and we start at 9:00 AM, so we can't meet William.

    # Next, Stephanie is available from 7:30-9:30 AM. We can meet her at 9:00 AM for 45 minutes.
    # But we start at 9:00 AM, and travel to Nob Hill takes 11 minutes, so we can't meet Stephanie at 9:00 AM.

    # So, let's try to meet Joseph at Alamo Square (11:30-12:45 PM, min 15 minutes)
    # Travel time from Fisherman's Wharf to Alamo Square is 20 minutes.
    # So, leave at 9:00, arrive at 9:20. But Joseph's window starts at 11:30. So can't meet him immediately.

    # Next, Karen at Russian Hill (2:30-7:45 PM, min 30 minutes)
    # Travel time from Fisherman's Wharf to Russian Hill is 7 minutes.
    # So, leave at 9:00, arrive at 9:07. But Karen's window starts at 14:30. So can't meet her immediately.

    # Kimberly at North Beach (3:45-7:15 PM, min 30 minutes)
    # Travel time from Fisherman's Wharf to North Beach is 6 minutes.
    # So, leave at 9:00, arrive at 9:06. But her window starts at 15:45. So can't meet her immediately.

    # Laura at The Castro (7:45-9:30 PM, min 105 minutes)
    # Daniel at Golden Gate Park (9:15-9:45 PM, min 15 minutes)

    # So, the only feasible meetings are Laura and Daniel, but they are in the evening.
    # We need to find a sequence that allows meeting some friends during the day.

    # Let's try to meet Joseph first:
    # Travel to Alamo Square: 20 minutes. So leave at 9:00, arrive at 9:20.
    # Joseph's window is 11:30-12:45. So earliest meeting is 11:30-11:45.
    # Then, from Alamo Square, where to next?

    # From Alamo Square to Russian Hill: 13 minutes.
    # Karen's window is 14:30-19:45. So leave Alamo Square at 11:45, arrive Russian Hill at 11:58.
    # Wait until 14:30 to meet Karen. Then meet Karen from 14:30-15:00.
    # Then, from Russian Hill to North Beach: 5 minutes.
    # Kimberly's window is 15:45-19:15. So leave Russian Hill at 15:00, arrive North Beach at 15:05.
    # Wait until 15:45, meet Kimberly from 15:45-16:15.
    # Then, from North Beach to The Castro: 22 minutes.
    # Laura's window is 19:45-21:30. So leave North Beach at 16:15, arrive The Castro at 16:37.
    # Wait until 19:45, meet Laura from 19:45-21:30 (105 minutes).
    # Then, from The Castro to Golden Gate Park: 11 minutes.
    # Daniel's window is 21:15-21:45. So leave The Castro at 21:30, arrive Golden Gate Park at 21:41.
    # But Daniel's window ends at 21:45, so only 4 minutes left, which is less than the required 15 minutes. So can't meet Daniel.

    # So this sequence allows meeting Joseph, Karen, Kimberly, and Laura.

    # Let's encode this sequence into the solver.

    # Define the sequence of meetings: Joseph, Karen, Kimberly, Laura
    sequence = ["Joseph", "Karen", "Kimberly", "Laura"]

    # Current time is 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Fisherman's Wharf"
    itinerary = []

    for name in sequence:
        friend = friends[name]
        location = friend["location"]
        travel_time = travel_times[(current_location, location)]
        arrival_time = current_time + travel_time
        start_window = time_to_minutes(friend["start"])
        end_window = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]

        # The meeting can start at max(start_window, arrival_time)
        meeting_start = max(arrival_time, start_window)
        meeting_end = meeting_start + min_duration

        # Check if meeting_end is within the window
        if meeting_end > end_window:
            # This sequence is not feasible; skip
            continue

        # Add to itinerary
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })

        # Update current time and location
        current_time = meeting_end
        current_location = location

    # Now, check if we can meet Daniel after Laura
    # From The Castro to Golden Gate Park: 11 minutes
    travel_time = travel_times[(current_location, "Golden Gate Park")]
    arrival_time = current_time + travel_time
    daniel = friends["Daniel"]
    start_window = time_to_minutes(daniel["start"])
    end_window = time_to_minutes(daniel["end"])
    min_duration = daniel["min_duration"]

    meeting_start = max(arrival_time, start_window)
    meeting_end = meeting_start + min_duration

    if meeting_end <= end_window:
        itinerary.append({
            "action": "meet",
            "person": "Daniel",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })

    # Output the itinerary
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

solve_scheduling()