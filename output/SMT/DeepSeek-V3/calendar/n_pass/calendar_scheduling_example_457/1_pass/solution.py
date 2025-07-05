from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the possible meeting start times in 30-minute increments from 9:00 to 16:30 (since meeting is 30 minutes)
    possible_start_times = [
        (9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (11, 30),
        (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30),
        (15, 0), (15, 30), (16, 0), (16, 30)
    ]
    
    # Create a Z3 variable for the meeting start time (index into possible_start_times)
    meeting_start = Int('meeting_start')
    s.add(meeting_start >= 0)
    s.add(meeting_start < len(possible_start_times))
    
    # Extract the start hour and minute for the chosen meeting time
    start_hour = Int('start_hour')
    start_minute = Int('start_minute')
    
    # Function to get hour and minute from index
    def get_time(index):
        return possible_start_times[index]
    
    # Constraint: start_hour and start_minute correspond to meeting_start's index
    for idx, (h, m) in enumerate(possible_start_times):
        s.add(Implies(meeting_start == idx, And(start_hour == h, start_minute == m)))
    
    # Define the meeting duration (30 minutes)
    meeting_duration = 30
    
    # Define each person's busy time slots
    # Each is a list of (start_hour, start_minute, end_hour, end_minute)
    andrea_busy = [(9, 30, 10, 30), (13, 30, 14, 30)]
    ruth_busy = [(12, 30, 13, 0), (15, 0, 15, 30)]
    steven_busy = [(10, 0, 10, 30), (11, 0, 11, 30), (12, 0, 12, 30), (13, 30, 14, 0), (15, 0, 16, 0)]
    grace_busy = []
    kyle_busy = [(9, 0, 9, 30), (10, 30, 12, 0), (12, 30, 13, 0), (13, 30, 15, 0), (15, 30, 16, 0), (16, 30, 17, 0)]
    elijah_busy = [(9, 0, 11, 0), (11, 30, 13, 0), (13, 30, 14, 0), (15, 30, 16, 0), (16, 30, 17, 0)]
    lori_busy = [(9, 0, 9, 30), (10, 0, 11, 30), (12, 0, 13, 30), (14, 0, 16, 0), (16, 30, 17, 0)]
    
    # Combine all busy times
    all_busy = {
        'Andrea': andrea_busy,
        'Ruth': ruth_busy,
        'Steven': steven_busy,
        'Grace': grace_busy,
        'Kyle': kyle_busy,
        'Elijah': elijah_busy,
        'Lori': lori_busy
    }
    
    # For each person, add constraints that the meeting does not overlap with their busy times
    for person, busy_slots in all_busy.items():
        for (busy_start_h, busy_start_m, busy_end_h, busy_end_m) in busy_slots:
            # Convert busy times to minutes since 9:00 for easier comparison
            busy_start = busy_start_h * 60 + busy_start_m - 9 * 60
            busy_end = busy_end_h * 60 + busy_end_m - 9 * 60
            
            # Meeting start and end in minutes since 9:00
            meeting_start_minutes = start_hour * 60 + start_minute - 9 * 60
            meeting_end_minutes = meeting_start_minutes + meeting_duration
            
            # The meeting should not overlap with the busy slot
            s.add(Or(
                meeting_end_minutes <= busy_start,
                meeting_start_minutes >= busy_end
            ))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_idx = m[meeting_start].as_long()
        start_h, start_m = possible_start_times[start_idx]
        end_h = start_h + (start_m + 30) // 60
        end_m = (start_m + 30) % 60
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_h:02d}:{start_m:02d}")
        print(f"End Time: {end_h:02d}:{end_m:02d}")
    else:
        print("No solution found")

solve_scheduling()