from z3 import *
import datetime

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the travel times between locations (in minutes)
    travel_times = {
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Presidio'): 18,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Presidio'): 14,
    }

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Available times for friends
    timothy_start = time_to_minutes("12:00")
    timothy_end = time_to_minutes("16:15")  # 4:15 PM
    mark_start = time_to_minutes("18:45")    # 6:45 PM
    mark_end = time_to_minutes("21:00")      # 9:00 PM
    joseph_start = time_to_minutes("16:45")  # 4:45 PM
    joseph_end = time_to_minutes("21:30")     # 9:30 PM

    # Minimum meeting durations in minutes
    timothy_min_duration = 105
    mark_min_duration = 60
    joseph_min_duration = 60

    # Variables for meeting start and end times
    t_start = Int('t_start')  # Timothy
    t_end = Int('t_end')
    m_start = Int('m_start')  # Mark
    m_end = Int('m_end')
    j_start = Int('j_start')  # Joseph
    j_end = Int('j_end')

    # Current location starts at Golden Gate Park at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes

    # Constraints for Timothy (Alamo Square)
    s.add(t_start >= timothy_start)
    s.add(t_end <= timothy_end)
    s.add(t_end - t_start >= timothy_min_duration)
    # Travel from Golden Gate Park to Alamo Square: 10 minutes
    s.add(t_start >= current_time + travel_times[('Golden Gate Park', 'Alamo Square')])

    # After meeting Timothy, decide where to go next: Presidio or Russian Hill
    # Let's assume we go to Russian Hill next (since Joseph is available earlier)
    # Travel from Alamo Square to Russian Hill: 13 minutes
    s.add(j_start >= t_end + travel_times[('Alamo Square', 'Russian Hill')])

    # Constraints for Joseph (Russian Hill)
    s.add(j_start >= joseph_start)
    s.add(j_end <= joseph_end)
    s.add(j_end - j_start >= joseph_min_duration)

    # After meeting Joseph, go to Presidio to meet Mark
    # Travel from Russian Hill to Presidio: 14 minutes
    s.add(m_start >= j_end + travel_times[('Russian Hill', 'Presidio')])

    # Constraints for Mark (Presidio)
    s.add(m_start >= mark_start)
    s.add(m_end <= mark_end)
    s.add(m_end - m_start >= mark_min_duration)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        t_s = model.eval(t_start).as_long()
        t_e = model.eval(t_end).as_long()
        j_s = model.eval(j_start).as_long()
        j_e = model.eval(j_end).as_long()
        m_s = model.eval(m_start).as_long()
        m_e = model.eval(m_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": minutes_to_time(t_s), "end_time": minutes_to_time(t_e)},
            {"action": "meet", "person": "Joseph", "start_time": minutes_to_time(j_s), "end_time": minutes_to_time(j_e)},
            {"action": "meet", "person": "Mark", "start_time": minutes_to_time(m_s), "end_time": minutes_to_time(m_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(result)