from z3 import *

def find_meeting_time():
    # Participants' busy slots in minutes since 9:00 (e.g., 9:00 is 0, 10:00 is 60, etc.)
    # Each entry is (start_minute, end_minute)
    busy_slots = {
        'Judy': [(4*60, 4*60 + 30), (7*60, 7*60 + 30)],
        'Olivia': [(1*60, 1*60 + 30), (3*60, 4*60), (5*60, 5*60 + 30)],
        'Eric': [],
        'Jacqueline': [(1*60, 1*60 + 30), (6*60, 6*60 + 30)],
        'Laura': [(0, 1*60), (1*60 + 30, 3*60), (4*60, 4*60 + 30), (5*60 + 30, 6*60), (6*60 + 30, 8*60)],
        'Tyler': [(0, 1*60), (2*60, 2*60 + 30), (3*60 + 30, 4*60), (5*60, 5*60 + 30), (6*60 + 30, 8*60)],
        'Lisa': [(0 + 30, 1*60 + 30), (2*60, 2*60 + 30), (3*60, 3*60 + 30), (4*60, 4*60 + 30), (5*60, 5*60 + 30), (7*60, 8*60)],
    }
    
    # Total work hours in minutes (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 8 * 60
    meeting_duration = 30
    
    # Create a Z3 solver instance
    s = Solver()
    
    # The meeting start time in minutes since 9:00
    start = Int('start')
    
    # Constraint: start time must be within work hours and leave room for the meeting
    s.add(start >= 0, start <= total_minutes - meeting_duration)
    
    # For each participant, ensure the meeting does not overlap with their busy slots
    for person, slots in busy_slots.items():
        for slot_start, slot_end in slots:
            # The meeting must not overlap with the busy slot
            # So either meeting ends before slot starts or starts after slot ends
            s.add(Or(
                start + meeting_duration <= slot_start,
                start >= slot_end
            ))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_minute = m[start].as_long()
        
        # Convert start_minute back to HH:MM format
        start_hour = 9 + start_minute // 60
        start_min = start_minute % 60
        end_minute = start_minute + meeting_duration
        end_hour = 9 + end_minute // 60
        end_min = end_minute % 60
        
        # Format the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_min:02d}")
        print(f"End Time: {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found")

find_meeting_time()