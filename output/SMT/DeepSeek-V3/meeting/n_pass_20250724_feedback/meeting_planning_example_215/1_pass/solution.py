from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times
    # Meeting with Jason at Fisherman's Wharf (4:00PM to 4:45PM, min 30 mins)
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')

    # Meeting with Jessica at Embarcadero (4:45PM to 7:00PM, min 30 mins)
    jessica_start = Int('jessica_start')
    jessica_end = Int('jessica_end')

    # Meeting with Sandra at Richmond District (6:30PM to 9:45PM, min 120 mins)
    sandra_start = Int('sandra_start')
    sandra_end = Int('sandra_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Time windows in minutes since 9:00 AM (540)
    jason_window_start = time_to_minutes("16:00") - 540  # 16:00 is 4:00 PM
    jason_window_end = time_to_minutes("16:45") - 540
    jessica_window_start = time_to_minutes("16:45") - 540
    jessica_window_end = time_to_minutes("19:00") - 540
    sandra_window_start = time_to_minutes("18:30") - 540
    sandra_window_end = time_to_minutes("21:45") - 540

    # Travel times from each location to another (in minutes)
    # Starting at Bayview at 0 minutes (9:00 AM)
    # Possible sequences:
    # Bayview -> Fisherman's Wharf (Jason) -> Embarcadero (Jessica) -> Richmond (Sandra)
    # Bayview -> Embarcadero (Jessica) -> Richmond (Sandra) -> (But can't meet Jason)
    # Bayview -> Richmond (Sandra) -> ... but can't meet others
    # So the feasible sequence is Bayview -> Fisherman's Wharf -> Embarcadero -> Richmond

    # Define travel times between locations in the sequence
    # Bayview to Fisherman's Wharf: 25 minutes
    travel_bayview_fisherman = 25
    # Fisherman's Wharf to Embarcadero: 8 minutes
    travel_fisherman_embarcadero = 8
    # Embarcadero to Richmond: 19 minutes
    travel_embarcadero_richmond = 19

    # Constraints for Jason's meeting
    s.add(jason_start >= jason_window_start)
    s.add(jason_end <= jason_window_end)
    s.add(jason_end - jason_start >= 30)  # min 30 minutes

    # Jason's meeting must start after arriving at Fisherman's Wharf (25 minutes from Bayview)
    s.add(jason_start >= travel_bayview_fisherman)

    # Constraints for Jessica's meeting
    s.add(jessica_start >= jessica_window_start)
    s.add(jessica_end <= jessica_window_end)
    s.add(jessica_end - jessica_start >= 30)  # min 30 minutes

    # Jessica's meeting must start after traveling from Fisherman's Wharf to Embarcadero
    s.add(jessica_start >= jason_end + travel_fisherman_embarcadero)

    # Constraints for Sandra's meeting
    s.add(sandra_start >= sandra_window_start)
    s.add(sandra_end <= sandra_window_end)
    s.add(sandra_end - sandra_start >= 120)  # min 120 minutes

    # Sandra's meeting must start after traveling from Embarcadero to Richmond
    s.add(sandra_start >= jessica_end + travel_embarcadero_richmond)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        # Extract times
        jason_s = model.eval(jason_start).as_long() + 540
        jason_e = model.eval(jason_end).as_long() + 540
        jessica_s = model.eval(jessica_start).as_long() + 540
        jessica_e = model.eval(jessica_end).as_long() + 540
        sandra_s = model.eval(sandra_start).as_long() + 540
        sandra_e = model.eval(sandra_end).as_long() + 540

        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"

        itinerary = [
            {"action": "meet", "person": "Jason", "start_time": minutes_to_time(jason_s), "end_time": minutes_to_time(jason_e)},
            {"action": "meet", "person": "Jessica", "start_time": minutes_to_time(jessica_s), "end_time": minutes_to_time(jessica_e)},
            {"action": "meet", "person": "Sandra", "start_time": minutes_to_time(sandra_s), "end_time": minutes_to_time(sandra_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))