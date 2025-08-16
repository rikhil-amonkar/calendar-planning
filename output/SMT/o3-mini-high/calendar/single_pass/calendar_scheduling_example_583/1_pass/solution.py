from z3 import *

def minutes_to_time_str(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Meeting parameters: duration of 30 minutes; working hours 9:00 (540) to 17:00 (1020)
    duration = 30
    work_start = 9 * 60      # 9:00 in minutes
    work_end = 17 * 60       # 17:00 in minutes

    # Create the Z3 optimizer instance
    opt = Optimize()

    # Define the meeting start time variable (minutes from midnight)
    meeting_start = Int('meeting_start')
    meeting_end = meeting_start + duration

    # Meeting must lie within the working hours.
    opt.add(meeting_start >= work_start)
    opt.add(meeting_end <= work_end)
    
    # Busy intervals (in minutes since midnight)
    # Lisa's busy times: 9:00-9:30, 10:30-11:00, 14:00-16:00
    busy_lisa = [(9*60, 9*60 + 30), (10*60 + 30, 11*60), (14*60, 16*60)]
    # Anthony's busy times: 9:00-9:30, 11:00-11:30, 12:30-13:30, 14:00-15:00, 15:30-16:00, 16:30-17:00
    busy_anthony = [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (12*60 + 30, 13*60 + 30),
                    (14*60, 15*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]
    
    # For each busy interval, add the constraint that the meeting does not overlap it.
    # That is, for each interval [b_start, b_end], either the meeting ends on/before b_start
    # or it starts on/after b_end.
    for (b_start, b_end) in busy_lisa + busy_anthony:
        opt.add(Or(meeting_end <= b_start, meeting_start >= b_end))
    
    # We want the earliest possible meeting time.
    opt.minimize(meeting_start)
    
    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        start_val = model[meeting_start].as_long()
        end_val = start_val + duration
        start_time_str = minutes_to_time_str(start_val)
        end_time_str = minutes_to_time_str(end_val)
        
        # Print the solution in the specified format.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time:", start_time_str)
        print("End Time:", end_time_str)
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()