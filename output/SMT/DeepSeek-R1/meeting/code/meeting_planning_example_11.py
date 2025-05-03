from z3 import *

def main():
    # Time in minutes after 9:00 AM
    T_depart = Int('T_depart')  # Departure time from Nob Hill
    T_start = Int('T_start')    # Start time of meeting
    T_end = Int('T_end')        # End time of meeting

    opt = Optimize()
    opt.add(T_depart >= 0)
    opt.add(T_start >= T_depart + 25)  # Travel time to Sunset District
    opt.add(T_start >= 300)            # 2:00PM (9AM + 300 mins)
    opt.add(T_end <= 690)              # 8:30PM (9AM + 690 mins)
    opt.add(T_end - T_start >= 75)     # Minimum meeting duration
    opt.minimize(T_end)                # Optimize for earliest possible end

    if opt.check() == sat:
        m = opt.model()
        depart = m.eval(T_depart).as_long()
        start = m.eval(T_start).as_long()
        end = m.eval(T_end).as_long()

        def time_str(mins):
            total_mins = 9 * 60 + mins
            hours, mins = divmod(total_mins, 60)
            am_pm = "AM" if hours < 12 else "PM"
            hours = hours if hours <= 12 else hours - 12
            return f"{hours}:{mins:02d}{am_pm}"

        print(f"Depart Nob Hill at {time_str(depart)}")
        print(f"Arrive Sunset District at {time_str(depart + 25)}")
        print(f"Meet Carol from {time_str(start)} to {time_str(end)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()