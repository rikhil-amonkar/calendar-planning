from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for each meeting's start and end times
    # Meeting with Timothy at Alamo Square
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    
    # Meeting with Mark at Presidio
    mark_start = Int('mark_start')
    mark_end = Int('mark_end')
    
    # Meeting with Joseph at Russian Hill
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    
    # Current time starts at 9:00 AM (540 minutes since midnight)
    current_time = 540  # 9:00 AM in minutes
    
    # Constraints for Timothy
    # Timothy is available from 12:00 PM (720) to 4:15 PM (975)
    s.add(timothy_start >= 720)
    s.add(timothy_end <= 975)
    s.add(timothy_end - timothy_start >= 105)  # at least 105 minutes
    
    # Travel from Golden Gate Park to Alamo Square takes 10 minutes
    # First activity is meeting Timothy at Alamo Square
    s.add(timothy_start >= current_time + 10)
    
    # Constraints for Mark
    # Mark is available from 6:45 PM (1185) to 9:00 PM (1260)
    s.add(mark_start >= 1185)
    s.add(mark_end <= 1260)
    s.add(mark_end - mark_start >= 60)  # at least 60 minutes
    
    # Constraints for Joseph
    # Joseph is available from 4:45 PM (1005) to 9:30 PM (1290)
    s.add(joseph_start >= 1005)
    s.add(joseph_end <= 1290)
    s.add(joseph_end - joseph_start >= 60)  # at least 60 minutes
    
    # Determine the order of meetings and travel times
    # We need to decide the order: Timothy -> Joseph -> Mark or Timothy -> Mark -> Joseph, etc.
    # Let's consider all possible orders and find a feasible one.
    
    # Option 1: Timothy -> Joseph -> Mark
    # Travel from Alamo Square to Russian Hill: 13 minutes
    # Travel from Russian Hill to Presidio: 14 minutes
    s.push()
    s.add(joseph_start >= timothy_end + 13)
    s.add(mark_start >= joseph_end + 14)
    
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (Timothy -> Joseph -> Mark):")
        print(f"Meet Timothy at Alamo Square from {m[timothy_start].as_long()//60}:{m[timothy_start].as_long()%60:02d} to {m[timothy_end].as_long()//60}:{m[timothy_end].as_long()%60:02d}")
        print(f"Meet Joseph at Russian Hill from {m[joseph_start].as_long()//60}:{m[joseph_start].as_long()%60:02d} to {m[joseph_end].as_long()//60}:{m[joseph_end].as_long()%60:02d}")
        print(f"Meet Mark at Presidio from {m[mark_start].as_long()//60}:{m[mark_start].as_long()%60:02d} to {m[mark_end].as_long()//60}:{m[mark_end].as_long()%60:02d}")
        return
    
    s.pop()
    
    # Option 2: Timothy -> Mark -> Joseph
    # Travel from Alamo Square to Presidio: 18 minutes
    # Travel from Presidio to Russian Hill: 14 minutes
    s.push()
    s.add(mark_start >= timothy_end + 18)
    s.add(joseph_start >= mark_end + 14)
    
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (Timothy -> Mark -> Joseph):")
        print(f"Meet Timothy at Alamo Square from {m[timothy_start].as_long()//60}:{m[timothy_start].as_long()%60:02d} to {m[timothy_end].as_long()//60}:{m[timothy_end].as_long()%60:02d}")
        print(f"Meet Mark at Presidio from {m[mark_start].as_long()//60}:{m[mark_start].as_long()%60:02d} to {m[mark_end].as_long()//60}:{m[mark_end].as_long()%60:02d}")
        print(f"Meet Joseph at Russian Hill from {m[joseph_start].as_long()//60}:{m[joseph_start].as_long()%60:02d} to {m[joseph_end].as_long()//60}:{m[joseph_end].as_long()%60:02d}")
        return
    
    s.pop()
    
    # Option 3: Timothy -> Joseph -> Mark (alternative)
    # If the first option didn't work, try adjusting times
    s.push()
    s.add(joseph_start >= timothy_end + 13)
    s.add(mark_start >= joseph_end + 14)
    # Ensure Joseph ends before Mark's latest start (since Mark's window is tight)
    s.add(joseph_end + 14 <= 1260)
    
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (Timothy -> Joseph -> Mark):")
        print(f"Meet Timothy at Alamo Square from {m[timothy_start].as_long()//60}:{m[timothy_start].as_long()%60:02d} to {m[timothy_end].as_long()//60}:{m[timothy_end].as_long()%60:02d}")
        print(f"Meet Joseph at Russian Hill from {m[joseph_start].as_long()//60}:{m[joseph_start].as_long()%60:02d} to {m[joseph_end].as_long()//60}:{m[joseph_end].as_long()%60:02d}")
        print(f"Meet Mark at Presidio from {m[mark_start].as_long()//60}:{m[mark_start].as_long()%60:02d} to {m[mark_end].as_long()//60}:{m[mark_end].as_long()%60:02d}")
        return
    
    s.pop()
    
    # If no feasible schedule found
    print("No feasible schedule found to meet all friends.")

solve_scheduling()