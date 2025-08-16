from z3 import *

def schedule_meeting():
    # Define variables
    solver_mon = Optimize()
    start_mon = Int('start_mon')
    solver_mon.add(start_mon >= 9 * 60)  # 9:00 AM
    solver_mon.add(start_mon <= 17 * 60 - 30)  # 4:30 PM (meeting must end by 5:00 PM)

    # Arthur's Monday meetings (in minutes since midnight)
    arthur_mon = [
        (11 * 60, 11 * 60 + 30),  # 11:00-11:30
        (13 * 60 + 30, 14 * 60),  # 13:30-14:00
        (15 * 60, 15 * 60 + 30)   # 15:00-15:30
    ]

    # Michael's Monday meetings
    michael_mon = [
        (9 * 60, 12 * 60),         # 9:00-12:00
        (12 * 60 + 30, 13 * 60),   # 12:30-13:00
        (14 * 60, 14 * 60 + 30),   # 14:00-14:30
        (15 * 60, 17 * 60)         # 15:00-17:00
    ]

    # Add constraints for Arthur and Michael on Monday
    for a_start, a_end in arthur_mon:
        solver_mon.add(Or(start_mon + 30 <= a_start, start_mon >= a_end))

    for m_start, m_end in michael_mon:
        solver_mon.add(Or(start_mon + 30 <= m_start, start_mon >= m_end))

    solver_mon.minimize(start_mon)

    # Check if a valid time exists on Monday
    if solver_mon.check() == sat:
        model_mon = solver_mon.model()
        start_mon_val = model_mon[start_mon].as_long()
        day = 0  # Monday
        start_time = start_mon_val
    else:
        # Try Wednesday
        solver_wed = Optimize()
        start_wed = Int('start_wed')
        solver_wed.add(start_wed >= 9 * 60)
        solver_wed.add(start_wed <= 17 * 60 - 30)

        # Arthur's Wednesday meetings
        arthur_wed = [
            (10 * 60, 10 * 60 + 30),  # 10:00-10:30
            (11 * 60, 11 * 60 + 30),  # 11:00-11:30
            (12 * 60, 12 * 60 + 30),  # 12:00-12:30
            (14 * 60, 14 * 60 + 30),  # 14:00-14:30
            (16 * 60, 16 * 60 + 30)   # 16:00-16:30
        ]

        # Michael's Wednesday meetings
        michael_wed = [
            (10 * 60, 12 * 60 + 30),  # 10:00-12:30
            (13 * 60, 13 * 60 + 30)   # 13:00-13:30
        ]

        # Add constraints for Arthur and Michael on Wednesday
        for a_start, a_end in arthur_wed:
            solver_wed.add(Or(start_wed + 30 <= a_start, start_wed >= a_end))

        for m_start, m_end in michael_wed:
            solver_wed.add(Or(start_wed + 30 <= m_start, start_wed >= m_end))

        solver_wed.minimize(start_wed)

        if solver_wed.check() == sat:
            model_wed = solver_wed.model()
            start_wed_val = model_wed[start_wed].as_long()
            day = 2  # Wednesday
            start_time = start_wed_val
        else:
            print("No valid meeting time found.")
            return

    # Convert start_time to day and time
    if day == 0:
        day_str = "Monday"
    else:
        day_str = "Wednesday"

    hours = start_time // 60
    minutes = start_time % 60
    start_str = f"{hours:02d}:{minutes:02d}"
    end_str = f"{(start_time + 30) // 60:02d}:{(start_time + 30) % 60:02d}"

    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")

# Run the scheduling function
schedule_meeting()