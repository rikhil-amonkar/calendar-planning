from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the possible time slots in 30-minute increments from 9:00 to 17:00
    time_slots = []
    start_hour = 9
    end_hour = 17
    for hour in range(start_hour, end_hour):
        for minute in [0, 30]:
            if hour == end_hour - 1 and minute == 30:
                continue  # 17:30 is beyond 17:00
            time_slots.append((hour, minute))
    
    # Create a variable for the chosen time slot (index in time_slots)
    slot = Int('slot')
    s.add(slot >= 0, slot < len(time_slots))
    
    # Margaret's blocked slots (each is a start and end time)
    margaret_blocked = [
        (9, 0, 10, 0),
        (10, 30, 11, 0),
        (11, 30, 12, 0),
        (13, 0, 13, 30),
        (15, 0, 15, 30)
    ]
    
    # Donna's blocked slots
    donna_blocked = [
        (14, 30, 15, 0),
        (16, 0, 16, 30)
    ]
    
    # Helen's blocked slots and preferences (doesn't want after 13:30)
    helen_blocked = [
        (9, 0, 9, 30),
        (10, 0, 11, 30),
        (13, 0, 14, 0),
        (14, 30, 15, 0),
        (15, 30, 17, 0)
    ]
    helen_no_after_13_30 = True
    
    # Function to check if a time slot (start_h, start_m) is blocked in a list of blocked intervals
    def is_blocked(start_h, start_m, blocked_intervals):
        start_time = start_h * 60 + start_m
        end_time = start_time + 30  # meeting duration is 30 minutes
        for (b_start_h, b_start_m, b_end_h, b_end_m) in blocked_intervals:
            b_start = b_start_h * 60 + b_start_m
            b_end = b_end_h * 60 + b_end_m
            if not (end_time <= b_start or start_time >= b_end):
                return True
        return False
    
    # Constraints for each participant's availability
    margaret_available = []
    donna_available = []
    helen_available = []
    
    for idx, (hour, minute) in enumerate(time_slots):
        # Check Margaret's availability
        margaret_ok = Not(is_blocked(hour, minute, margaret_blocked))
        margaret_available.append(If(slot == idx, margaret_ok, True))
        
        # Check Donna's availability
        donna_ok = Not(is_blocked(hour, minute, donna_blocked))
        donna_available.append(If(slot == idx, donna_ok, True))
        
        # Check Helen's availability and preference
        helen_ok = Not(is_blocked(hour, minute, helen_blocked))
        if helen_no_after_13_30:
            # Also, the meeting must start before or at 13:00 to end by 13:30
            meeting_start_time = hour * 60 + minute
            helen_ok = And(helen_ok, meeting_start_time <= 13 * 60 + 0)
        helen_available.append(If(slot == idx, helen_ok, True))
    
    # Add constraints that for the chosen slot, all participants are available
    s.add(And(
        And([Or(Not(slot == i), margaret_available[i]) for i in range(len(time_slots))]),
        And([Or(Not(slot == i), donna_available[i]) for i in range(len(time_slots))]),
        And([Or(Not(slot == i), helen_available[i]) for i in range(len(time_slots))])
    ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        chosen_slot = m[slot].as_long()
        hour, minute = time_slots[chosen_slot]
        
        # Calculate end time
        end_minute = minute + 30
        end_hour = hour
        if end_minute >= 60:
            end_hour += 1
            end_minute -= 60
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        start_time_str = f"{hour:02d}:{minute:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()