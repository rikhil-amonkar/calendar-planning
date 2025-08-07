from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert times to minutes since 00:00 for easier arithmetic
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Availability windows in minutes
    melissa_start = time_to_minutes("08:30")
    melissa_end = time_to_minutes("20:00")
    nancy_start = time_to_minutes("19:45")
    nancy_end = time_to_minutes("22:00")
    emily_start = time_to_minutes("16:45")
    emily_end = time_to_minutes("22:00")

    # Travel times (in minutes)
    travel = {
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Richmond District'): 7,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Presidio'): 7
    }

    # Variables for meeting start and end times (in minutes since 00:00)
    melissa_meet_start = Int('melissa_meet_start')
    melissa_meet_end = Int('melissa_meet_end')
    nancy_meet_start = Int('nancy_meet_start')
    nancy_meet_end = Int('nancy_meet_end')
    emily_meet_start = Int('emily_meet_start')
    emily_meet_end = Int('emily_meet_end')

    # Constraints for Melissa
    s.add(melissa_meet_start >= melissa_start)
    s.add(melissa_meet_end <= melissa_end)
    s.add(melissa_meet_end - melissa_meet_start >= 15)  # Minimum 15 minutes

    # Constraints for Nancy
    s.add(nancy_meet_start >= nancy_start)
    s.add(nancy_meet_end <= nancy_end)
    s.add(nancy_meet_end - nancy_meet_start >= 105)  # Minimum 105 minutes

    # Constraints for Emily
    s.add(emily_meet_start >= emily_start)
    s.add(emily_meet_end <= emily_end)
    s.add(emily_meet_end - emily_meet_start >= 120)  # Minimum 120 minutes

    # Arrival time at Fisherman's Wharf: 9:00 AM (540 minutes)
    arrival_time = time_to_minutes("09:00")

    # Possible meeting orders:
    # We need to schedule meetings with Melissa, Nancy, and Emily, considering travel times.
    # Given the time constraints, the feasible order is likely:
    # 1. Melissa (Golden Gate Park) - since she's available earliest.
    # 2. Emily (Richmond District) - after Melissa.
    # 3. Nancy (Presidio) - after Emily.

    # Assume the order: Melissa -> Emily -> Nancy
    # Travel from Fisherman's Wharf to Golden Gate Park: 25 minutes.
    s.add(melissa_meet_start >= arrival_time + 25)

    # Travel from Golden Gate Park to Richmond District: 7 minutes.
    s.add(emily_meet_start >= melissa_meet_end + 7)

    # Travel from Richmond District to Presidio: 7 minutes.
    s.add(nancy_meet_start >= emily_meet_end + 7)

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert to human-readable times
        itinerary = []
        # Melissa meeting
        melissa_s = m.eval(melissa_meet_start).as_long()
        melissa_e = m.eval(melissa_meet_end).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Melissa",
            "start_time": minutes_to_time(melissa_s),
            "end_time": minutes_to_time(melissa_e)
        })
        # Emily meeting
        emily_s = m.eval(emily_meet_start).as_long()
        emily_e = m.eval(emily_meet_end).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Emily",
            "start_time": minutes_to_time(emily_s),
            "end_time": minutes_to_time(emily_e)
        })
        # Nancy meeting
        nancy_s = m.eval(nancy_meet_start).as_long()
        nancy_e = m.eval(nancy_meet_end).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Nancy",
            "start_time": minutes_to_time(nancy_s),
            "end_time": minutes_to_time(nancy_e)
        })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))