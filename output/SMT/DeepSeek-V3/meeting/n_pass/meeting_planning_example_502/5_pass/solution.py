from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting times (minutes since 9:00 AM)
    rebecca_start, rebecca_end = Ints('rebecca_start rebecca_end')
    stephanie_start, stephanie_end = Ints('stephanie_start stephanie_end')
    karen_start, karen_end = Ints('karen_start karen_end')
    brian_start, brian_end = Ints('brian_start brian_end')
    steven_start, steven_end = Ints('steven_start steven_end')

    # Meeting duration constraints
    s.add(rebecca_end - rebecca_start >= 30)
    s.add(stephanie_end - stephanie_start >= 105)
    s.add(karen_end - karen_start >= 15)
    s.add(brian_end - brian_start >= 30)
    s.add(steven_end - steven_start >= 120)

    # Time window constraints
    s.add(rebecca_start >= 0, rebecca_end <= 135)      # 9:00-11:15 AM
    s.add(stephanie_start >= 120, stephanie_end <= 360) # 11:00 AM-3:00 PM
    s.add(karen_start >= 285, karen_end <= 450)        # 1:45-4:30 PM
    s.add(brian_start >= 360, brian_end <= 495)        # 3:00-5:15 PM
    s.add(steven_start >= 330, steven_end <= 705)      # 2:30-8:45 PM

    # Travel time constraints
    s.add(rebecca_start >= 10)  # FD to FW: 10 min
    s.add(stephanie_start >= rebecca_end + 25)  # FW to GGP: 25 min
    s.add(karen_start >= stephanie_end + 23)    # GGP to CT: 23 min
    s.add(brian_start >= karen_end + 7)         # CT to US: 7 min
    s.add(steven_start >= brian_end + 10)       # US to NB: 10 min

    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        def format_time(minutes):
            total_min = 540 + minutes  # 9:00 AM = 540 minutes
            hours = total_min // 60
            mins = total_min % 60
            period = "AM" if hours < 12 else "PM"
            hour = hours if hours <= 12 else hours - 12
            return f"{hour}:{mins:02d} {period}"
        
        meetings = [
            ("Rebecca", "Fisherman's Wharf", m[rebecca_start], m[rebecca_end]),
            ("Stephanie", "Golden Gate Park", m[stephanie_start], m[stephanie_end]),
            ("Karen", "Chinatown", m[karen_start], m[karen_end]),
            ("Brian", "Union Square", m[brian_start], m[brian_end]),
            ("Steven", "North Beach", m[steven_start], m[steven_end])
        ]
        
        for name, location, start, end in meetings:
            start_time = format_time(start.as_long())
            end_time = format_time(end.as_long())
            print(f"Meet {name} at {location} from {start_time} to {end_time}")
    else:
        print("No feasible schedule found.")

solve_scheduling()