from z3 import *

def main():
    # Time in minutes after 9:00 AM
    T_depart = Int('T_depart')  # Departure time from Presidio
    T_start = Int('T_start')    # Start time of meeting
    T_end = Int('T_end')        # End time of meeting

    opt = Optimize()
    opt.add(T_depart >= 0)
    opt.add(T_start >= T_depart + 22)  # Travel time to Union Square
    opt.add(T_start >= 135)            # 11:15AM (9AM + 135 mins)
    opt.add(T_end <= 495)              # 5:15PM (9AM + 495 mins)
    opt.add(T_end - T_start >= 105)    # Minimum meeting duration
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

        print(f"Depart Presidio at {time_str(depart)}")
        print(f"Arrive Union Square at {time_str(depart + 22)}")
        print(f"Meet Andrew from {time_str(start)} to {time_str(end)}")  # Fixed quote
    else:
        print("No solution found")

if __name__ == "__main__":
    main()