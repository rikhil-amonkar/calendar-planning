from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Optimize()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    max_time = 765  # 9:45 PM is 765 minutes after 9:00 AM

    # Meeting durations in minutes
    timothy_min_duration = 120
    patricia_min_duration = 90
    ashley_min_duration = 45

    # Define variables
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')
    ashley_start = Int('ashley_start')
    ashley_end = Int('ashley_end')

    # Time windows for each friend (in minutes since 9:00 AM)
    patricia_window_start = 570  # 6:30 PM
    patricia_window_end = 765    # 9:45 PM
    ashley_window_start = 690    # 8:30 PM
    ashley_window_end = 705      # 9:15 PM
    timothy_window_start = 45    # 9:45 AM
    timothy_window_end = 525     # 5:45 PM

    # Add constraints for each meeting
    s.add(timothy_start >= timothy_window_start)
    s.add(timothy_end <= timothy_window_end)
    s.add(timothy_end == timothy_start + timothy_min_duration)

    s.add(patricia_start >= patricia_window_start)
    s.add(patricia_end <= patricia_window_end)
    s.add(patricia_end == patricia_start + patricia_min_duration)

    s.add(ashley_start >= ashley_window_start)
    s.add(ashley_end <= ashley_window_end)
    s.add(ashley_end == ashley_start + ashley_min_duration)

    # Travel times between locations (in minutes)
    travel = {
        ('Russian Hill', 'Embarcadero'): 8,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Mission District'): 20,
        ('Russian Hill', 'Mission District'): 16,
        ('Mission District', 'Nob Hill'): 12,
    }

    # Define possible meeting sequences
    # Option 1: Timothy (Embarcadero) -> Patricia (Nob Hill)
    s.add(Implies(And(timothy_start >= 0, patricia_start >= 0),
                 patricia_start >= timothy_end + travel[('Embarcadero', 'Nob Hill')]))

    # Option 2: Ashley (Mission District) -> Patricia (Nob Hill)
    s.add(Implies(And(ashley_start >= 0, patricia_start >= 0),
                 patricia_start >= ashley_end + travel[('Mission District', 'Nob Hill')]))

    # Option 3: Timothy (Embarcadero) -> Ashley (Mission District) -> Patricia (Nob Hill)
    s.add(Implies(And(timothy_start >= 0, ashley_start >= 0, patricia_start >= 0),
                 And(ashley_start >= timothy_end + travel[('Embarcadero', 'Mission District')],
                     patricia_start >= ashley_end + travel[('Mission District', 'Nob Hill')])))

    # Option 4: Just meet Patricia
    s.add(Implies(patricia_start >= 0, patricia_start >= travel[('Russian Hill', 'Nob Hill')]))

    # Maximize the number of friends met
    num_meetings = Int('num_meetings')
    s.add(num_meetings == If(timothy_start >= 0, 1, 0) + 
                         If(ashley_start >= 0, 1, 0) + 
                         If(patricia_start >= 0, 1, 0))
    s.maximize(num_meetings)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        if m[timothy_start] is not None:
            itinerary.append({
                "action": "meet", 
                "person": "Timothy", 
                "start_time": minutes_to_time(m[timothy_start].as_long()), 
                "end_time": minutes_to_time(m[timothy_end].as_long())
            })
        if m[ashley_start] is not None:
            itinerary.append({
                "action": "meet", 
                "person": "Ashley", 
                "start_time": minutes_to_time(m[ashley_start].as_long()), 
                "end_time": minutes_to_time(m[ashley_end].as_long())
            })
        if m[patricia_start] is not None:
            itinerary.append({
                "action": "meet", 
                "person": "Patricia", 
                "start_time": minutes_to_time(m[patricia_start].as_long()), 
                "end_time": minutes_to_time(m[patricia_end].as_long())
            })
        return {"itinerary": sorted(itinerary, key=lambda x: x["start_time"])}
    else:
        return {"itinerary": []}

def minutes_to_time(minutes):
    total_minutes = 540 + minutes  # 9:00 AM is 540 minutes past midnight
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))