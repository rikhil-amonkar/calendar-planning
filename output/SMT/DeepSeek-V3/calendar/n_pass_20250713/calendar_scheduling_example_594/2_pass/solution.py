from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes (0.5 hours)

    # Define the busy slots for Adam and Roy in minutes since 9:00
    adam_busy = [
        (9 * 60 + 30, 10 * 60),      # 9:30-10:00
        (12 * 60 + 30, 13 * 60),      # 12:30-13:00
        (14 * 60 + 30, 15 * 60),      # 14:30-15:00
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]
    roy_busy = [
        (10 * 60, 11 * 60),           # 10:00-11:00
        (11 * 60 + 30, 13 * 60),      # 11:30-13:00
        (13 * 60 + 30, 14 * 60 + 30), # 13:30-14:30
        (16 * 60 + 30, 17 * 60)       # 16:30-17:00
    ]

    # Create a Z3 Optimize instance (for minimization)
    opt = Optimize()

    # The start time of the meeting (in minutes since 9:00)
    start = Int('start')

    # Constraints: start time must be within work hours and leave room for the meeting
    opt.add(start >= work_start)
    opt.add(start + meeting_duration <= work_end)

    # Function to add constraints that the meeting does not overlap with any busy slot
    def add_no_overlap_constraints(busy_slots):
        for slot in busy_slots:
            opt.add(Or(
                start + meeting_duration <= slot[0],  # Meeting ends before the busy slot starts
                start >= slot[1]                     # Meeting starts after the busy slot ends
            ))

    # Add no-overlap constraints for Adam and Roy
    add_no_overlap_constraints(adam_busy)
    add_no_overlap_constraints(roy_busy)

    # We want the earliest possible meeting, so we minimize the start time
    opt.minimize(start)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        start_time = m[start].as_long()
        
        # Convert start time from minutes to HH:MM format
        hours = start_time // 60
        minutes = start_time % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_time = start_time + meeting_duration
        end_hours = end_time // 60
        end_minutes = end_time % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Print the solution in the required format
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

find_meeting_time()