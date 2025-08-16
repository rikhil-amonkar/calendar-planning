from z3 import *

def main():
    # Create a Z3 solver instance
    s = Solver()

    # Define variables:
    # "day" represents the meeting day.
    # We use an integer where 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
    day = Int('day')
    # "meeting_start" represents the start time in minutes from midnight.
    # For example, 9:00 = 9*60 = 540 and 17:00 = 1020.
    meeting_start = Int('meeting_start')
    duration = 30  # meeting duration in minutes
    meeting_end = meeting_start + duration

    # Constraint: The meeting must occur during work hours, [9:00, 17:00],
    # i.e., meeting_start must be at least 9:00 (540) and meeting_end at most 17:00 (1020).
    s.add(meeting_start >= 9*60)
    s.add(meeting_end <= 17*60)

    # Constraint: The meeting can only be scheduled on Monday (0), Tuesday (1),
    # Wednesday (2) or Thursday (3).
    s.add(Or(day == 0, day == 1, day == 2, day == 3))

    # Participant schedules:
    # Julie is free the whole week.
    #
    # Ruth is busy:
    #   - Monday: 9:00-17:00
    #   - Tuesday: 9:00-17:00
    #   - Wednesday: 9:00-17:00
    #   - Thursday: busy from 9:00 to 11:00, 11:30 to 14:30, and 15:00 to 17:00.
    #
    # Thus, on Monday, Tuesday, and Wednesday Ruth is unavailable for any meeting 
    # during work hours. The only possible day is Thursday.
    s.add(day == 3)

    # On Thursday, Ruth is free only in the following intervals during work hours:
    #   • Free interval 1: 11:00 to 11:30, and
    #   • Free interval 2: 14:30 to 15:00.
    #
    # However, Julie prefers to avoid meetings on Thursday before 11:30.
    # That rule forces us to select interval 2.
    #
    # We add the following constraints:
    # 1. Enforce Julie's preference: if the meeting is on Thursday, meeting must start at or after 11:30.
    s.add(meeting_start >= 11*60 + 30)  # 11:30 in minutes is 690.
    
    # 2. Force the meeting to fit in free interval 2:
    #    The only slot available that is after 11:30 is 14:30 to 15:00.
    free_slot2 = And(meeting_start == 14*60 + 30, meeting_end <= (14*60 + 30) + 30)
    s.add(free_slot2)

    # Check if the constraints are satisfiable.
    if s.check() == sat:
        m = s.model()
        chosen_day = m[day].as_long()
        chosen_start = m[meeting_start].as_long()
        chosen_end = chosen_start + duration

        # Map integer days to day names
        day_map = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
        day_str = day_map[chosen_day]

        # A helper function to convert minutes to the "HH:MM" format.
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_time_str = minutes_to_time(chosen_start)
        end_time_str = minutes_to_time(chosen_end)

        # Print the solution in the required format.
        result = f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}"
        print(result)
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()