from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their constraints
    friends = {
        "Betty": {
            "location": "Presidio",
            "available_start": "10:15",
            "available_end": "21:30",
            "min_duration": 45,
        },
        "David": {
            "location": "Richmond District",
            "available_start": "13:00",
            "available_end": "20:15",
            "min_duration": 90,
        },
        "Barbara": {
            "location": "Fisherman's Wharf",
            "available_start": "09:15",
            "available_end": "20:15",
            "min_duration": 120,
        }
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Embarcadero": {
            "Presidio": 20,
            "Richmond District": 21,
            "Fisherman's Wharf": 6,
        },
        "Presidio": {
            "Embarcadero": 20,
            "Richmond District": 7,
            "Fisherman's Wharf": 19,
        },
        "Richmond District": {
            "Embarcadero": 19,
            "Presidio": 7,
            "Fisherman's Wharf": 18,
        },
        "Fisherman's Wharf": {
            "Embarcadero": 8,
            "Presidio": 17,
            "Richmond District": 18,
        }
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

    # Create Z3 variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f"start_{name}")
        end = Int(f"end_{name}")
        meeting_vars[name] = (start, end)

    # Current location starts at Embarcadero
    current_location = "Embarcadero"
    arrival_time = 0  # 9:00 AM is time 0

    # Constraints for each friend
    for name in friends:
        start, end = meeting_vars[name]
        info = friends[name]
        available_start = time_to_minutes(info["available_start"])
        available_end = time_to_minutes(info["available_end"])
        min_duration = info["min_duration"]

        # Meeting must be within available time
        s.add(start >= available_start)
        s.add(end <= available_end)
        # Meeting duration must be at least min_duration
        s.add(end - start >= min_duration)

    # All meetings must start after arrival_time (initially 0)
    # And we need to sequence meetings considering travel times
    # We'll assume an order of meetings to simplify. Alternatively, could use Z3 to explore permutations.
    # Here, we'll try Barbara -> Betty -> David as one possible order.

    # Option 1: Barbara -> Betty -> David
    # Barbara at Fisherman's Wharf
    barbara_start, barbara_end = meeting_vars["Barbara"]
    s.add(barbara_start >= time_to_minutes("09:15"))
    # Travel from Embarcadero to Fisherman's Wharf: 6 minutes
    s.add(barbara_start >= arrival_time + 6)

    # Betty at Presidio
    betty_start, betty_end = meeting_vars["Betty"]
    # Travel from Fisherman's Wharf to Presidio: 17 minutes
    s.add(betty_start >= barbara_end + 17)

    # David at Richmond District
    david_start, david_end = meeting_vars["David"]
    # Travel from Presidio to Richmond District: 7 minutes
    s.add(david_start >= betty_end + 7)

    # Also, ensure that David's meeting ends by 20:15 (which is already in the friend's constraints)

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in ["Barbara", "Betty", "David"]:
            start, end = meeting_vars[name]
            start_val = model.eval(start).as_long()
            end_val = model.eval(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        return {"itinerary": itinerary}
    else:
        # Try another order if the first one fails
        s.reset()
        s = Solver()
        for name in friends:
            start, end = meeting_vars[name]
            info = friends[name]
            available_start = time_to_minutes(info["available_start"])
            available_end = time_to_minutes(info["available_end"])
            min_duration = info["min_duration"]
            s.add(start >= available_start)
            s.add(end <= available_end)
            s.add(end - start >= min_duration)

        # Order: Barbara -> David -> Betty
        barbara_start, barbara_end = meeting_vars["Barbara"]
        s.add(barbara_start >= arrival_time + 6)  # Travel to Fisherman's Wharf

        david_start, david_end = meeting_vars["David"]
        # Travel from Fisherman's Wharf to Richmond District: 18 minutes
        s.add(david_start >= barbara_end + 18)

        betty_start, betty_end = meeting_vars["Betty"]
        # Travel from Richmond District to Presidio: 7 minutes
        s.add(betty_start >= david_end + 7)

        if s.check() == sat:
            model = s.model()
            itinerary = []
            for name in ["Barbara", "David", "Betty"]:
                start, end = meeting_vars[name]
                start_val = model.eval(start).as_long()
                end_val = model.eval(end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
            return {"itinerary": itinerary}
        else:
            # Try another order: Betty -> Barbara -> David
            s.reset()
            s = Solver()
            for name in friends:
                start, end = meeting_vars[name]
                info = friends[name]
                available_start = time_to_minutes(info["available_start"])
                available_end = time_to_minutes(info["available_end"])
                min_duration = info["min_duration"]
                s.add(start >= available_start)
                s.add(end <= available_end)
                s.add(end - start >= min_duration)

            # Order: Betty -> Barbara -> David
            betty_start, betty_end = meeting_vars["Betty"]
            # Travel from Embarcadero to Presidio: 20 minutes
            s.add(betty_start >= arrival_time + 20)

            barbara_start, barbara_end = meeting_vars["Barbara"]
            # Travel from Presidio to Fisherman's Wharf: 19 minutes
            s.add(barbara_start >= betty_end + 19)

            david_start, david_end = meeting_vars["David"]
            # Travel from Fisherman's Wharf to Richmond District: 18 minutes
            s.add(david_start >= barbara_end + 18)

            if s.check() == sat:
                model = s.model()
                itinerary = []
                for name in ["Betty", "Barbara", "David"]:
                    start, end = meeting_vars[name]
                    start_val = model.eval(start).as_long()
                    end_val = model.eval(end).as_long()
                    itinerary.append({
                        "action": "meet",
                        "person": name,
                        "start_time": minutes_to_time(start_val),
                        "end_time": minutes_to_time(end_val)
                    })
                return {"itinerary": itinerary}
            else:
                return {"itinerary": []}  # No feasible schedule found

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))