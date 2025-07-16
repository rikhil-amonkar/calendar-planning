from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    mark_start = Int('mark_start')
    mark_end = Int('mark_end')
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Convert all times to minutes since midnight
    arrival_time = 540  # 9:00AM
    timothy_window_start = 720  # 12:00PM
    timothy_window_end = 975    # 4:15PM
    mark_window_start = 1185    # 6:45PM
    mark_window_end = 1260      # 9:00PM
    joseph_window_start = 1005  # 4:45PM
    joseph_window_end = 1290    # 9:30PM

    # Meeting durations
    min_timothy_duration = 105
    min_mark_duration = 60
    min_joseph_duration = 60

    # Travel times (minutes)
    travel_times = {
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Alamo Square', 'Presidio'): 18,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Presidio', 'Russian Hill'): 14,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Presidio', 'Alamo Square'): 18
    }

    # Base constraints for each meeting
    s.add(timothy_start >= timothy_window_start)
    s.add(timothy_end <= timothy_window_end)
    s.add(timothy_end - timothy_start >= min_timothy_duration)
    s.add(timothy_start >= arrival_time + travel_times[('Golden Gate Park', 'Alamo Square')])

    s.add(mark_start >= mark_window_start)
    s.add(mark_end <= mark_window_end)
    s.add(mark_end - mark_start >= min_mark_duration)

    s.add(joseph_start >= joseph_window_start)
    s.add(joseph_end <= joseph_window_end)
    s.add(joseph_end - joseph_start >= min_joseph_duration)

    # Try different meeting orders
    orders = [
        ('Timothy -> Joseph -> Mark', 
         [('Alamo Square', 'Russian Hill', timothy_end, joseph_start),
          ('Russian Hill', 'Presidio', joseph_end, mark_start)]),
        ('Timothy -> Mark -> Joseph',
         [('Alamo Square', 'Presidio', timothy_end, mark_start),
          ('Presidio', 'Russian Hill', mark_end, joseph_start)])
    ]

    for order_name, transitions in orders:
        s.push()
        for from_loc, to_loc, prev_end, next_start in transitions:
            s.add(next_start >= prev_end + travel_times[(from_loc, to_loc)])
        
        if s.check() == sat:
            m = s.model()
            print(f"Feasible schedule found ({order_name}):")
            print(f"- Meet Timothy: {format_time(m[timothy_start].as_long())} to {format_time(m[timothy_end].as_long())}")
            print(f"- Meet Joseph: {format_time(m[joseph_start].as_long())} to {format_time(m[joseph_end].as_long())}")
            print(f"- Meet Mark: {format_time(m[mark_start].as_long())} to {format_time(m[mark_end].as_long())}")
            return
        s.pop()

    print("No feasible schedule found to meet all friends.")

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    ampm = "AM" if hours < 12 else "PM"
    if hours > 12:
        hours -= 12
    return f"{hours}:{mins:02d} {ampm}"

solve_scheduling()