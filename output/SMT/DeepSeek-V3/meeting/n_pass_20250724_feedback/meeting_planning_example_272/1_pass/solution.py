from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Meeting durations in minutes
    timothy_duration = 120
    ashley_duration = 45
    patricia_duration = 90

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Available time slots
    timothy_start_available = time_to_minutes("09:45")  # 9:45 AM
    timothy_end_available = time_to_minutes("17:45")    # 5:45 PM
    ashley_start_available = time_to_minutes("20:30")   # 8:30 PM
    ashley_end_available = time_to_minutes("21:15")     # 9:15 PM
    patricia_start_available = time_to_minutes("18:30") # 6:30 PM
    patricia_end_available = time_to_minutes("21:45")    # 9:45 PM

    # Variables for meeting start times (in minutes since midnight)
    timothy_start = Int('timothy_start')
    ashley_start = Int('ashley_start')
    patricia_start = Int('patricia_start')

    # Constraints for meeting within available times
    s.add(timothy_start >= timothy_start_available)
    s.add(timothy_start + timothy_duration <= timothy_end_available)
    s.add(ashley_start >= ashley_start_available)
    s.add(ashley_start + ashley_duration <= ashley_end_available)
    s.add(patricia_start >= patricia_start_available)
    s.add(patricia_start + patricia_duration <= patricia_end_available)

    # Initial location is Russian Hill at 9:00 AM (540 minutes)
    initial_time = 540  # 9:00 AM in minutes

    # Travel times between locations (in minutes)
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

    # Locations of each friend
    friend_locations = {
        'Timothy': 'Embarcadero',
        'Ashley': 'Mission District',
        'Patricia': 'Nob Hill'
    }

    # Order of meetings: Timothy -> Patricia -> Ashley
    # This is a possible order that might satisfy all constraints
    # We'll model the travel times between these meetings

    # First meeting: Timothy at Embarcadero
    # Travel from Russian Hill to Embarcadero: 8 minutes
    s.add(timothy_start >= initial_time + 8)

    # Second meeting: Patricia at Nob Hill
    # Travel from Embarcadero to Nob Hill: 10 minutes
    s.add(patricia_start >= timothy_start + timothy_duration + 10)

    # Third meeting: Ashley at Mission District
    # Travel from Nob Hill to Mission District: 13 minutes
    s.add(ashley_start >= patricia_start + patricia_duration + 13)

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        # Get the start times
        timothy_start_val = model.eval(timothy_start).as_long()
        ashley_start_val = model.eval(ashley_start).as_long()
        patricia_start_val = model.eval(patricia_start).as_long()

        # Create the itinerary
        itinerary = [
            {
                "action": "meet",
                "person": "Timothy",
                "start_time": minutes_to_time(timothy_start_val),
                "end_time": minutes_to_time(timothy_start_val + timothy_duration)
            },
            {
                "action": "meet",
                "person": "Patricia",
                "start_time": minutes_to_time(patricia_start_val),
                "end_time": minutes_to_time(patricia_start_val + patricia_duration)
            },
            {
                "action": "meet",
                "person": "Ashley",
                "start_time": minutes_to_time(ashley_start_val),
                "end_time": minutes_to_time(ashley_start_val + ashley_duration)
            }
        ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))