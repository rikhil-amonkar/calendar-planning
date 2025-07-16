from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    # Meeting with Timothy at Embarcadero
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    
    # Meeting with Ashley at Mission District
    ashley_start = Int('ashley_start')
    ashley_end = Int('ashley_end')
    
    # Meeting with Patricia at Nob Hill
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')

    # Define availability windows (in minutes since 9:00 AM)
    # Timothy: 9:45 AM to 5:45 PM (45 to 1065 minutes)
    # Ashley: 8:30 PM to 9:15 PM (690 to 735 minutes)
    # Patricia: 6:30 PM to 9:45 PM (570 to 765 minutes)

    # Add meeting duration constraints
    s.add(timothy_end - timothy_start >= 120)  # At least 2 hours with Timothy
    s.add(ashley_end - ashley_start >= 45)     # At least 45 minutes with Ashley
    s.add(patricia_end - patricia_start >= 90)  # At least 1.5 hours with Patricia

    # Add availability window constraints
    s.add(timothy_start >= 45, timothy_end <= 1065)
    s.add(ashley_start >= 690, ashley_end <= 735)
    s.add(patricia_start >= 570, patricia_end <= 765)

    # Define travel times (in minutes)
    travel = {
        ('Russian Hill', 'Embarcadero'): 8,
        ('Embarcadero', 'Mission District'): 20,
        ('Mission District', 'Nob Hill'): 12,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Nob Hill', 'Mission District'): 13
    }

    # Try different meeting sequences

    # Sequence 1: Timothy -> Ashley -> Patricia
    s.push()
    s.add(timothy_start >= 8)  # Travel from Russian Hill to Embarcadero
    s.add(ashley_start >= timothy_end + travel[('Embarcadero', 'Mission District')])
    s.add(patricia_start >= ashley_end + travel[('Mission District', 'Nob Hill')])
    
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"1. Meet Timothy at Embarcadero from {convert_to_time(m[timothy_start].as_long())} to {convert_to_time(m[timothy_end].as_long())}")
        print(f"   (Travel time: 8 min from Russian Hill to Embarcadero)")
        print(f"2. Travel to Mission District (20 min)")
        print(f"3. Meet Ashley at Mission District from {convert_to_time(m[ashley_start].as_long())} to {convert_to_time(m[ashley_end].as_long())}")
        print(f"4. Travel to Nob Hill (12 min)")
        print(f"5. Meet Patricia at Nob Hill from {convert_to_time(m[patricia_start].as_long())} to {convert_to_time(m[patricia_end].as_long())}")
        return
    s.pop()

    # Sequence 2: Timothy -> Patricia -> Ashley
    s.push()
    s.add(timothy_start >= 8)  # Travel from Russian Hill to Embarcadero
    s.add(patricia_start >= timothy_end + travel[('Embarcadero', 'Nob Hill')])
    s.add(ashley_start >= patricia_end + travel[('Nob Hill', 'Mission District')])
    
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"1. Meet Timothy at Embarcadero from {convert_to_time(m[timothy_start].as_long())} to {convert_to_time(m[timothy_end].as_long())}")
        print(f"   (Travel time: 8 min from Russian Hill to Embarcadero)")
        print(f"2. Travel to Nob Hill (10 min)")
        print(f"3. Meet Patricia at Nob Hill from {convert_to_time(m[patricia_start].as_long())} to {convert_to_time(m[patricia_end].as_long())}")
        print(f"4. Travel to Mission District (13 min)")
        print(f"5. Meet Ashley at Mission District from {convert_to_time(m[ashley_start].as_long())} to {convert_to_time(m[ashley_end].as_long())}")
        return
    s.pop()

    # If no feasible schedule found
    print("No feasible schedule found that meets all constraints.")

def convert_to_time(minutes):
    """Convert minutes since 9:00 AM to HH:MM format"""
    total_min = 540 + minutes  # 9:00 AM is 540 minutes from midnight
    hours = total_min // 60
    mins = total_min % 60
    return f"{hours}:{mins:02d}"

solve_scheduling()