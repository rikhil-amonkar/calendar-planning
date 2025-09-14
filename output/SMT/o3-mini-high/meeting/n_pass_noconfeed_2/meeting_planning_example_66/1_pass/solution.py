#!/usr/bin/env python3
import json
from z3 import Optimize, Int, If, sat

# Function to convert minutes-since-midnight into 24-hour time format (e.g., "9:00" or "13:30")
def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # ----------------------------
    # Input Parameters / Constants
    # ----------------------------
    # Arrival at Nob Hill: 9:00 AM -> 9*60 = 540 minutes since midnight
    arrival_nobhill = 9 * 60  # 540

    # Robert's availability at Presidio: 11:15 AM to 5:45 PM
    robert_start = 11 * 60 + 15  # 675 minutes
    robert_end   = 17 * 60 + 45  # 1065 minutes

    # Travel times (in minutes)
    travel_nobhill_to_presidio = 17
    travel_presidio_to_nobhill = 18

    # Minimum required meeting duration with Robert (in minutes)
    required_meeting_duration = 120

    # ----------------------------
    # Create the SMT optimizer instance
    # ----------------------------
    opt = Optimize()

    # Decision variables (in minutes from midnight)
    # d is the departure time from Nob Hill.
    d = Int('depart_time')
    # meeting_end is the time when the meeting with Robert ends.
    meeting_end = Int('meeting_end')

    # We define meeting_start as the later of the arrival time at Presidio and Robert's available start.
    # Arrival time at Presidio is d + travel_nobhill_to_presidio.
    meeting_start = If(d + travel_nobhill_to_presidio < robert_start, robert_start, d + travel_nobhill_to_presidio)

    # ----------------------------
    # Add constraints
    # ----------------------------
    # 1. You cannot depart before your arrival to Nob Hill.
    opt.add(d >= arrival_nobhill)
    # 2. The meeting must end no later than Robert's available end time.
    opt.add(meeting_end <= robert_end)
    # 3. You want at least the minimum meeting duration.
    opt.add(meeting_end >= meeting_start + required_meeting_duration)

    # ----------------------------
    # Optimization objectives
    # ----------------------------
    # Our primary goal is to maximize the meeting duration.
    meeting_duration = meeting_end - meeting_start
    h1 = opt.maximize(meeting_duration)
    # Secondary goal: maximize the departure time from Nob Hill to minimize idle waiting time.
    h2 = opt.maximize(d)

    # ----------------------------
    # Solve the optimization problem
    # ----------------------------
    if opt.check() == sat:
        model = opt.model()
    else:
        print(json.dumps({"error": "No valid schedule could be found."}))
        return

    # Extract the computed times
    depart_val = model[d].as_long()
    # meeting_start is an expression; evaluate it from the model.
    meeting_start_val = model.evaluate(meeting_start).as_long()
    meeting_end_val = model[meeting_end].as_long()
    travel_arrival_val = depart_val + travel_nobhill_to_presidio  # Actual arrival at Presidio
    return_arrival_val = meeting_end_val + travel_presidio_to_nobhill  # Arrival back at Nob Hill

    # ----------------------------
    # Build the itinerary (accounting for travel and meeting)
    # ----------------------------
    itinerary = []
    # Travel from Nob Hill to Presidio
    itinerary.append({
        "action": "travel",
        "location": "Presidio",
        "person": "",
        "start_time": minutes_to_time(depart_val),
        "end_time": minutes_to_time(travel_arrival_val)
    })
    # Meeting with Robert at Presidio
    itinerary.append({
        "action": "meet",
        "location": "Presidio",
        "person": "Robert",
        "start_time": minutes_to_time(meeting_start_val),
        "end_time": minutes_to_time(meeting_end_val)
    })
    # Travel back from Presidio to Nob Hill
    itinerary.append({
        "action": "travel",
        "location": "Nob Hill",
        "person": "",
        "start_time": minutes_to_time(meeting_end_val),
        "end_time": minutes_to_time(return_arrival_val)
    })

    # ----------------------------
    # Output the result as a JSON-formatted dictionary
    # ----------------------------
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()