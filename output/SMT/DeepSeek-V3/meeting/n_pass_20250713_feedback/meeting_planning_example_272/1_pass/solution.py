from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(hour, minute):
        return hour * 60 + minute

    # Convert back to readable time
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Arrival time at Russian Hill: 9:00 AM (540 minutes)
    arrival_time = time_to_minutes(9, 0)

    # Friends' availability and required meeting durations
    # Patricia: Nob Hill, 18:30-21:45, min 90 minutes
    patricia_start_window = time_to_minutes(18, 30)
    patricia_end_window = time_to_minutes(21, 45)
    patricia_min_duration = 90

    # Ashley: Mission District, 20:30-21:15, min 45 minutes
    ashley_start_window = time_to_minutes(20, 30)
    ashley_end_window = time_to_minutes(21, 15)
    ashley_min_duration = 45

    # Timothy: Embarcadero, 9:45-17:45, min 120 minutes
    timothy_start_window = time_to_minutes(9, 45)
    timothy_end_window = time_to_minutes(17, 45)
    timothy_min_duration = 120

    # Travel times dictionary: (from, to) -> minutes
    travel_times = {
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Embarcadero'): 19,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Mission District'): 20,
    }

    # Decision variables: start and end times for each meeting
    # We need to decide the order of meetings. Let's assume the order is Timothy, Patricia, Ashley.
    # This is one possible order; other orders may be possible but we'll start with this.
    # Variables for Timothy's meeting
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    # Variables for Patricia's meeting
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')
    # Variables for Ashley's meeting
    ashley_start = Int('ashley_start')
    ashley_end = Int('ashley_end')

    # Constraints for Timothy
    s.add(timothy_start >= timothy_start_window)
    s.add(timothy_end <= timothy_end_window)
    s.add(timothy_end == timothy_start + timothy_min_duration)

    # Constraints for Patricia
    s.add(patricia_start >= patricia_start_window)
    s.add(patricia_end <= patricia_end_window)
    s.add(patricia_end == patricia_start + patricia_min_duration)

    # Constraints for Ashley
    s.add(ashley_start >= ashley_start_window)
    s.add(ashley_end <= ashley_end_window)
    s.add(ashley_end == ashley_start + ashley_min_duration)

    # Travel constraints
    # From Russian Hill to Embarcadero (first meeting: Timothy)
    s.add(timothy_start >= arrival_time + travel_times[('Russian Hill', 'Embarcadero')])

    # From Embarcadero to Nob Hill (Timothy to Patricia)
    s.add(patricia_start >= timothy_end + travel_times[('Embarcadero', 'Nob Hill')])

    # From Nob Hill to Mission District (Patricia to Ashley)
    s.add(ashley_start >= patricia_end + travel_times[('Nob Hill', 'Mission District')])

    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        timothy_s = m.eval(timothy_start).as_long()
        timothy_e = m.eval(timothy_end).as_long()
        patricia_s = m.eval(patricia_start).as_long()
        patricia_e = m.eval(patricia_end).as_long()
        ashley_s = m.eval(ashley_start).as_long()
        ashley_e = m.eval(ashley_end).as_long()

        print("SOLUTION:")
        print(f"Meet Timothy at Embarcadero from {minutes_to_time(timothy_s)} to {minutes_to_time(timothy_e)}")
        print(f"Then travel to Nob Hill to meet Patricia from {minutes_to_time(patricia_s)} to {minutes_to_time(patricia_e)}")
        print(f"Then travel to Mission District to meet Ashley from {minutes_to_time(ashley_s)} to {minutes_to_time(ashley_e)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()