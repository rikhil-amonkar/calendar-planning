from z3 import *
import datetime

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define the friends and their constraints
    friends = [
        {
            "name": "Helen",
            "location": "North Beach",
            "available_start": "09:00",
            "available_end": "17:00",
            "min_duration": 15,
        },
        {
            "name": "Kevin",
            "location": "Mission District",
            "available_start": "10:45",
            "available_end": "14:45",
            "min_duration": 45,
        },
        {
            "name": "Amanda",
            "location": "Alamo Square",
            "available_start": "19:45",
            "available_end": "21:00",
            "min_duration": 60,
        },
        {
            "name": "Betty",
            "location": "Financial District",
            "available_start": "19:00",
            "available_end": "21:45",
            "min_duration": 90,
        }
    ]

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Pacific Heights": {
            "North Beach": 9,
            "Financial District": 13,
            "Alamo Square": 10,
            "Mission District": 15
        },
        "North Beach": {
            "Pacific Heights": 8,
            "Financial District": 8,
            "Alamo Square": 16,
            "Mission District": 18
        },
        "Financial District": {
            "Pacific Heights": 13,
            "North Beach": 7,
            "Alamo Square": 17,
            "Mission District": 17
        },
        "Alamo Square": {
            "Pacific Heights": 10,
            "North Beach": 15,
            "Financial District": 17,
            "Mission District": 10
        },
        "Mission District": {
            "Pacific Heights": 16,
            "North Beach": 17,
            "Financial District": 17,
            "Alamo Square": 11
        }
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

    # Current location and time
    current_location = "Pacific Heights"
    current_time = time_to_minutes("09:00")

    # Variables for each meeting: start and end times
    meetings = []
    for friend in friends:
        name = friend["name"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]

        start = Int(f'start_{name}')
        end = Int(f'end_{name}')

        # Constraints for the meeting
        s.add(start >= available_start)
        s.add(end <= available_end)
        s.add(end == start + min_duration)
        s.add(start >= 0)
        s.add(end >= 0)

        meetings.append({
            "name": name,
            "location": friend["location"],
            "start": start,
            "end": end,
            "min_duration": min_duration,
            "available_start": available_start,
            "available_end": available_end
        })

    # Define the order of meetings as a permutation
    # We'll use a list to represent the order and enforce constraints accordingly
    # For simplicity, we'll assume the order is Helen -> Kevin -> Amanda -> Betty
    # and add constraints to ensure travel times are respected

    # Start at Pacific Heights at 09:00
    prev_end = current_time
    prev_location = current_location

    # Try to meet Helen first
    helen = next(f for f in meetings if f["name"] == "Helen")
    travel_time = travel_times[prev_location][helen["location"]]
    s.add(helen["start"] >= prev_end + travel_time)

    # After Helen, go to Kevin
    kevin = next(f for f in meetings if f["name"] == "Kevin")
    travel_time = travel_times[helen["location"]][kevin["location"]]
    s.add(kevin["start"] >= helen["end"] + travel_time)

    # After Kevin, go to Amanda
    amanda = next(f for f in meetings if f["name"] == "Amanda")
    travel_time = travel_times[kevin["location"]][amanda["location"]]
    s.add(amanda["start"] >= kevin["end"] + travel_time)

    # After Amanda, go to Betty
    betty = next(f for f in meetings if f["name"] == "Betty")
    travel_time = travel_times[amanda["location"]][betty["location"]]
    s.add(betty["start"] >= amanda["end"] + travel_time)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for meeting in meetings:
            start_val = model[meeting["start"]].as_long()
            end_val = model[meeting["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        # If the first order fails, try a different order
        # For example, try meeting Kevin first, then Helen, then Amanda, then Betty
        s.reset()
        s = Solver()

        # Re-add the meeting constraints
        for meeting in meetings:
            name = meeting["name"]
            available_start = meeting["available_start"]
            available_end = meeting["available_end"]
            min_duration = meeting["min_duration"]
            start = Int(f'start_{name}')
            end = Int(f'end_{name}')
            s.add(start >= available_start)
            s.add(end <= available_end)
            s.add(end == start + min_duration)
            s.add(start >= 0)
            s.add(end >= 0)

        # Start at Pacific Heights at 09:00
        prev_end = current_time
        prev_location = current_location

        # Try to meet Kevin first
        kevin = next(f for f in meetings if f["name"] == "Kevin")
        travel_time = travel_times[prev_location][kevin["location"]]
        s.add(kevin["start"] >= prev_end + travel_time)

        # After Kevin, go to Helen
        helen = next(f for f in meetings if f["name"] == "Helen")
        travel_time = travel_times[kevin["location"]][helen["location"]]
        s.add(helen["start"] >= kevin["end"] + travel_time)

        # After Helen, go to Amanda
        amanda = next(f for f in meetings if f["name"] == "Amanda")
        travel_time = travel_times[helen["location"]][amanda["location"]]
        s.add(amanda["start"] >= helen["end"] + travel_time)

        # After Amanda, go to Betty
        betty = next(f for f in meetings if f["name"] == "Betty")
        travel_time = travel_times[amanda["location"]][betty["location"]]
        s.add(betty["start"] >= amanda["end"] + travel_time)

        if s.check() == sat:
            model = s.model()
            itinerary = []
            for meeting in meetings:
                start_val = model[meeting["start"]].as_long()
                end_val = model[meeting["end"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": meeting["name"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(solution)