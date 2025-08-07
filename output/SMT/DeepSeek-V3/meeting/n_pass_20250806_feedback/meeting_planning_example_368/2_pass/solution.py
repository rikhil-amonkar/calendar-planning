from z3 import *
import datetime

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')

    # Convert availability windows to minutes since 9:00 AM
    # Arrival time: 9:00 AM (0 minutes)
    joseph_available_start = (8*60 + 30) - (9*60)  # 8:30 AM is -30 minutes (but we start at 9:00 AM)
    joseph_available_end = (19*60 + 15) - (9*60)    # 7:15 PM is 10*60 + 15 = 615 minutes
    nancy_available_start = (11*60) - (9*60)        # 11:00 AM is 120 minutes
    nancy_available_end = (16*60) - (9*60)          # 4:00 PM is 420 minutes
    jason_available_start = (16*60 + 45) - (9*60)   # 4:45 PM is 465 minutes
    jason_available_end = (21*60 + 45) - (9*60)     # 9:45 PM is 765 minutes
    jeffrey_available_start = (10*60 + 30) - (9*60) # 10:30 AM is 90 minutes
    jeffrey_available_end = (15*60 + 45) - (9*60)   # 3:45 PM is 405 minutes

    # Add constraints for each meeting's duration and availability
    s.add(joseph_end == joseph_start + 60)  # Joseph: 60 minutes
    s.add(joseph_start >= 23)  # Earliest start is 9:00 AM + 23 min travel = 9:23 AM
    s.add(joseph_end <= joseph_available_end)

    s.add(nancy_end == nancy_start + 90)    # Nancy: 90 minutes
    s.add(nancy_start >= nancy_available_start)
    s.add(nancy_end <= nancy_available_end)

    s.add(jason_end == jason_start + 15)    # Jason: 15 minutes
    s.add(jason_start >= jason_available_start)
    s.add(jason_end <= jason_available_end)

    s.add(jeffrey_end == jeffrey_start + 45) # Jeffrey: 45 minutes
    s.add(jeffrey_start >= jeffrey_available_start)
    s.add(jeffrey_end <= jeffrey_available_end)

    # Travel times (in minutes)
    travel = {
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Financial District'): 19,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Financial District'): 11,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('North Beach', 'Bayview'): 22,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Russian Hill'): 10,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'North Beach'): 7,
    }

    # Define the order of meetings and account for travel times
    # Start by meeting Joseph at Russian Hill (after traveling from Bayview)
    # Then meet Jeffrey at Financial District
    # Then meet Nancy at Alamo Square
    # Finally meet Jason at North Beach
    s.add(joseph_start >= 23)  # Travel from Bayview to Russian Hill takes 23 minutes
    s.add(jeffrey_start >= joseph_end + travel[('Russian Hill', 'Financial District')])  # Travel from Russian Hill to Financial District takes 11 minutes
    s.add(nancy_start >= jeffrey_end + travel[('Financial District', 'Alamo Square')])  # Travel from Financial District to Alamo Square takes 17 minutes
    s.add(jason_start >= nancy_end + travel[('Alamo Square', 'North Beach')])  # Travel from Alamo Square to North Beach takes 16 minutes

    # Try to solve
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to HH:MM format
        base_time = datetime.datetime(2000, 1, 1, 9, 0)  # 9:00 AM base
        def minutes_to_time(minutes):
            time = base_time + datetime.timedelta(minutes=minutes)
            return time.strftime("%H:%M")

        joseph_start_time = minutes_to_time(m[joseph_start].as_long())
        joseph_end_time = minutes_to_time(m[joseph_end].as_long())
        jeffrey_start_time = minutes_to_time(m[jeffrey_start].as_long())
        jeffrey_end_time = minutes_to_time(m[jeffrey_end].as_long())
        nancy_start_time = minutes_to_time(m[nancy_start].as_long())
        nancy_end_time = minutes_to_time(m[nancy_end].as_long())
        jason_start_time = minutes_to_time(m[jason_start].as_long())
        jason_end_time = minutes_to_time(m[jason_end].as_long())

        itinerary = [
            {"action": "meet", "person": "Joseph", "start_time": joseph_start_time, "end_time": joseph_end_time},
            {"action": "meet", "person": "Jeffrey", "start_time": jeffrey_start_time, "end_time": jeffrey_end_time},
            {"action": "meet", "person": "Nancy", "start_time": nancy_start_time, "end_time": nancy_end_time},
            {"action": "meet", "person": "Jason", "start_time": jason_start_time, "end_time": jason_end_time},
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}  # No feasible schedule found

# Run the solver and print the result
print(solve_scheduling_problem())