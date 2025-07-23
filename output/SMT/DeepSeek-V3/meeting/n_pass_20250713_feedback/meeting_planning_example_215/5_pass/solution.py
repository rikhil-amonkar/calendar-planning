from z3 import *

def solve_scheduling():
    s = Solver()

    # Meeting times in minutes since 9:00 AM (540)
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    jessica_start = Int('jessica_start')
    jessica_end = Int('jessica_end')
    sandra_start = Int('sandra_start')
    sandra_end = Int('sandra_end')

    # Travel times in minutes
    bayview_to_fisherman = 25
    fisherman_to_embarcadero = 8
    embarcadero_to_richmond = 21

    # Availability windows
    jason_window = (960, 1005)    # 4:00 PM - 4:45 PM
    jessica_window = (1005, 1140) # 4:45 PM - 7:00 PM
    sandra_window = (1170, 1305)  # 6:30 PM - 9:45 PM

    # Meeting duration constraints
    s.add(jason_end - jason_start >= 30)
    s.add(jessica_end - jessica_start >= 30)
    s.add(sandra_end - sandra_start >= 120)

    # Strict availability constraints
    s.add(jason_start >= jason_window[0], jason_end <= jason_window[1])
    s.add(jessica_start >= jessica_window[0], jessica_end <= jessica_window[1])
    s.add(sandra_start >= sandra_window[0], sandra_end <= sandra_window[1])

    # Travel time constraints
    s.add(jason_start >= 540 + bayview_to_fisherman)  # Arrive at Fisherman's Wharf
    s.add(jessica_start >= jason_end + fisherman_to_embarcadero)
    s.add(sandra_start >= jessica_end + embarcadero_to_richmond)

    # Additional constraints to prevent early scheduling
    s.add(jason_start >= jason_window[0])  # Force Jason's meeting to be in his window
    s.add(jessica_start >= jessica_window[0])
    s.add(sandra_start >= sandra_window[0])

    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")

        def format_time(minutes):
            total = 540 + m[minutes].as_long()
            hours = total // 60
            mins = total % 60
            period = "PM" if hours >= 12 else "AM"
            if hours > 12: hours -= 12
            return f"{hours}:{mins:02d} {period}"

        print("Meeting with Jason at Fisherman's Wharf:")
        print(f"Start: {format_time(jason_start)}")
        print(f"End: {format_time(jason_end)}")

        print("\nMeeting with Jessica at Embarcadero:")
        print(f"Start: {format_time(jessica_start)}")
        print(f"End: {format_time(jessica_end)}")

        print("\nMeeting with Sandra at Richmond District:")
        print(f"Start: {format_time(sandra_start)}")
        print(f"End: {format_time(sandra_end)}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()