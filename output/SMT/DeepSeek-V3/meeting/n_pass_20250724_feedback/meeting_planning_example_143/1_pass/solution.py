from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Available time slots
    karen_start = time_to_minutes("18:45")
    karen_end = time_to_minutes("20:15")
    mark_start = time_to_minutes("13:00")
    mark_end = time_to_minutes("17:45")

    # Travel times in minutes
    travel = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Embarcadero"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
    }

    # Meeting durations in minutes
    karen_duration = 90
    mark_duration = 120

    # Variables for meeting start times (in minutes since midnight)
    meet_karen_start = Int('meet_karen_start')
    meet_mark_start = Int('meet_mark_start')

    # Initial location is North Beach at 9:00 AM (540 minutes since midnight)
    initial_time = time_to_minutes("09:00")
    initial_location = "North Beach"

    # Option 1: Meet Mark first, then Karen
    # Travel from North Beach to Embarcadero: 6 minutes
    mark_arrival_time = initial_time + travel[("North Beach", "Embarcadero")]
    # Mark's meeting must start >= max(mark_arrival_time, mark_start)
    s.add(meet_mark_start >= mark_arrival_time)
    s.add(meet_mark_start >= mark_start)
    s.add(meet_mark_start + mark_duration <= mark_end)
    # After meeting Mark, travel to Pacific Heights: 11 minutes
    karen_arrival_time = meet_mark_start + mark_duration + travel[("Embarcadero", "Pacific Heights")]
    s.add(meet_karen_start >= karen_arrival_time)
    s.add(meet_karen_start >= karen_start)
    s.add(meet_karen_start + karen_duration <= karen_end)

    # Check if this option is feasible
    if s.check() == sat:
        m = s.model()
        mark_s = m.eval(meet_mark_start).as_long()
        mark_e = mark_s + mark_duration
        karen_s = m.eval(meet_karen_start).as_long()
        karen_e = karen_s + karen_duration
        itinerary = [
            {"action": "meet", "person": "Mark", "start_time": minutes_to_time(mark_s), "end_time": minutes_to_time(mark_e)},
            {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_s), "end_time": minutes_to_time(karen_e)}
        ]
        return {"itinerary": itinerary}
    else:
        # Option 2: Meet Karen first, then Mark
        s = Solver()
        # Travel from North Beach to Pacific Heights: 8 minutes
        karen_arrival_time = initial_time + travel[("North Beach", "Pacific Heights")]
        s.add(meet_karen_start >= karen_arrival_time)
        s.add(meet_karen_start >= karen_start)
        s.add(meet_karen_start + karen_duration <= karen_end)
        # After meeting Karen, travel to Embarcadero: 10 minutes
        mark_arrival_time = meet_karen_start + karen_duration + travel[("Pacific Heights", "Embarcadero")]
        s.add(meet_mark_start >= mark_arrival_time)
        s.add(meet_mark_start >= mark_start)
        s.add(meet_mark_start + mark_duration <= mark_end)

        if s.check() == sat:
            m = s.model()
            karen_s = m.eval(meet_karen_start).as_long()
            karen_e = karen_s + karen_duration
            mark_s = m.eval(meet_mark_start).as_long()
            mark_e = mark_s + mark_duration
            itinerary = [
                {"action": "meet", "person": "Karen", "start_time": minutes_to_time(karen_s), "end_time": minutes_to_time(karen_e)},
                {"action": "meet", "person": "Mark", "start_time": minutes_to_time(mark_s), "end_time": minutes_to_time(mark_e)}
            ]
            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}  # No feasible schedule

# Execute and print the solution
solution = solve_scheduling()
print(solution)