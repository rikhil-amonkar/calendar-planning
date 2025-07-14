from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Karen's availability: 6:45 PM (18:45) to 8:15 PM (20:15) -> 18*60 + 45 = 1125 to 20*60 + 15 = 1215
    # Mark's availability: 1:00 PM (13:00) to 5:45 PM (17:45) -> 13*60 = 780 to 17*60 + 45 = 1065

    # Define variables for meeting start and end times
    mark_start = Int('mark_start')
    mark_end = Int('mark_end')
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Define travel times
    travel_nb_to_emb = 6  # North Beach to Embarcadero
    travel_emb_to_ph = 11  # Embarcadero to Pacific Heights

    # Start at North Beach at 9:00 AM (540 minutes)
    arrival_embarcadero = 540 + travel_nb_to_emb  # 9:06 AM

    # Meeting Mark must start after arrival at Embarcadero and within his window (780 to 1065)
    s.add(mark_start >= arrival_embarcadero)
    s.add(mark_start >= 780)  # 1:00 PM
    s.add(mark_end == mark_start + 120)  # 120 minutes meeting
    s.add(mark_end <= 1065)   # 5:45 PM

    # Travel from Embarcadero to Pacific Heights after meeting Mark
    departure_embarcadero = mark_end
    arrival_pacific_heights = departure_embarcadero + travel_emb_to_ph

    # Meeting Karen must start after arrival at Pacific Heights and within her window (1125 to 1215 - 90)
    s.add(karen_start >= arrival_pacific_heights)
    s.add(karen_start >= 1125)  # 6:45 PM
    s.add(karen_end == karen_start + 90)  # 90 minutes meeting
    s.add(karen_end <= 1215)    # 8:15 PM

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert times back to hours and minutes
        def minutes_to_time(minutes):
            total_minutes = minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h}:{m:02d}"

        mark_start_time = m.evaluate(mark_start).as_long()
        mark_end_time = m.evaluate(mark_end).as_long()
        karen_start_time = m.evaluate(karen_start).as_long()
        karen_end_time = m.evaluate(karen_end).as_long()
        arrival_pacific_heights_time = m.evaluate(arrival_pacific_heights).as_long()

        print("SOLUTION:")
        print(f"Meet Mark from {minutes_to_time(mark_start_time)} to {minutes_to_time(mark_end_time)}")
        print(f"Travel to Pacific Heights, arriving at {minutes_to_time(arrival_pacific_heights_time)}")
        print(f"Meet Karen from {minutes_to_time(karen_start_time)} to {minutes_to_time(karen_end_time)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()