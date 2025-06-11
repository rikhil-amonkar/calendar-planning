from z3 import *

def min_to_time(m):
    hour = 9 + m // 60
    minutes = m % 60
    am_pm = "AM" if hour < 12 else "PM"
    display_hour = hour % 12
    if display_hour == 0:
        display_hour = 12
    return f"{display_hour}:{minutes:02d}{am_pm}"

# Try meeting both friends in order: Embarcadero -> Financial District -> Alamo Square
s1, d1, s2, d2 = Ints('s1 d1 s2 d2')
solver1 = Solver()
solver1.add(s1 >= 5, d1 >= 90, s1 + d1 <= 150)
solver1.add(s2 >= s1 + d1 + 17, s2 >= 75, d2 >= 30, s2 + d2 <= 705)

if solver1.check() == sat:
    model = solver1.model()
    s1_val = model[s1].as_long()
    d1_val = model[d1].as_long()
    s2_val = model[s2].as_long()
    d2_val = model[d2].as_long()
    schedule = "Met both friends: Stephanie and John.\n"
    schedule += f"  Start at Embarcadero at 9:00AM.\n"
    schedule += f"  Travel to Financial District (5 minutes), arriving at {min_to_time(s1_val)}.\n"
    schedule += f"  Meet Stephanie from {min_to_time(s1_val)} to {min_to_time(s1_val + d1_val)} ({d1_val} minutes).\n"
    schedule += f"  Travel to Alamo Square (17 minutes), arriving at {min_to_time(s1_val + d1_val + 17)}.\n"
    schedule += f"  Meet John from {min_to_time(s2_val)} to {min_to_time(s2_val + d2_val)} ({d2_val} minutes).\n"
    print("SOLUTION: " + schedule)
else:
    # Try meeting both in reverse order: Embarcadero -> Alamo Square -> Financial District
    s1_o2, d1_o2, s2_o2, d2_o2 = Ints('s1_o2 d1_o2 s2_o2 d2_o2')
    solver2 = Solver()
    solver2.add(s2_o2 >= 19, s2_o2 >= 75, d2_o2 >= 30, s2_o2 + d2_o2 <= 705)
    solver2.add(s1_o2 >= s2_o2 + d2_o2 + 17, d1_o2 >= 90, s1_o2 + d1_o2 <= 150)
    
    if solver2.check() == sat:
        model = solver2.model()
        s1_val = model[s1_o2].as_long()
        d1_val = model[d1_o2].as_long()
        s2_val = model[s2_o2].as_long()
        d2_val = model[d2_o2].as_long()
        schedule = "Met both friends: Stephanie and John.\n"
        schedule += f"  Start at Embarcadero at 9:00AM.\n"
        schedule += f"  Travel to Alamo Square (19 minutes), arriving at {min_to_time(19)}.\n"
        schedule += f"  Meet John from {min_to_time(s2_val)} to {min_to_time(s2_val + d2_val)} ({d2_val} minutes).\n"
        schedule += f"  Travel to Financial District (17 minutes), arriving at {min_to_time(s2_val + d2_val + 17)}.\n"
        schedule += f"  Meet Stephanie from {min_to_time(s1_val)} to {min_to_time(s1_val + d1_val)} ({d1_val} minutes).\n"
        print("SOLUTION: " + schedule)
    else:
        # Try meeting only Stephanie
        s1_o3, d1_o3 = Ints('s1_o3 d1_o3')
        solver3 = Solver()
        solver3.add(s1_o3 >= 5, d1_o3 >= 90, s1_o3 + d1_o3 <= 150)
        if solver3.check() == sat:
            model = solver3.model()
            s1_val = model[s1_o3].as_long()
            d1_val = model[d1_o3].as_long()
            schedule = "Met only Stephanie.\n"
            schedule += f"  Start at Embarcadero at 9:00AM.\n"
            schedule += f"  Travel to Financial District (5 minutes), arriving at {min_to_time(s1_val)}.\n"
            schedule += f"  Meet Stephanie from {min_to_time(s1_val)} to {min_to_time(s1_val + d1_val)} ({d1_val} minutes).\n"
            print("SOLUTION: " + schedule)
        else:
            # Try meeting only John
            s2_o4, d2_o4 = Ints('s2_o4 d2_o4')
            solver4 = Solver()
            solver4.add(s2_o4 >= 19, s2_o4 >= 75, d2_o4 >= 30, s2_o4 + d2_o4 <= 705)
            if solver4.check() == sat:
                model = solver4.model()
                s2_val = model[s2_o4].as_long()
                d2_val = model[d2_o4].as_long()
                schedule = "Met only John.\n"
                schedule += f"  Start at Embarcadero at 9:00AM.\n"
                schedule += f"  Travel to Alamo Square (19 minutes), arriving at {min_to_time(19)}.\n"
                schedule += f"  Meet John from {min_to_time(s2_val)} to {min_to_time(s2_val + d2_val)} ({d2_val} minutes).\n"
                print("SOLUTION: " + schedule)
            else:
                print("SOLUTION: Could not meet any friend.")